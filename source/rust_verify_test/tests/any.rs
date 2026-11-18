#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// `core::any::Any` is declared to Verus with no methods, which makes `dyn Any` a
// legal type. The coercion axiom carries the erased type's identity through it,
// so an erased value can be asked what it is -- the question `type_id` cannot
// answer and a downcast needs.

test_verify_one_file! {
    #[test] dyn_any_is_a_legal_type verus_code! {
        use vstd::prelude::*;
        use core::any::Any;
        use verus_builtin::{type_id, type_id_of};
        struct C(u64);
        fn erase(c: &C) -> (r: &dyn Any)
            ensures type_id_of(r) == type_id::<C>(),
        {
            c
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] dyn_any_is verus_code! {
        use vstd::prelude::*;
        use core::any::Any;
        struct C(u64);
        struct D(u64);
        fn accepts(c: &C) -> (r: bool)
            ensures r,
        {
            let d: &dyn Any = c;
            d.is::<C>()
        }
        fn rejects(c: &C) -> (r: bool)
            ensures !r,
        {
            let d: &dyn Any = c;
            d.is::<D>()
        }
    } => Ok(())
}

// Identity is decoration-sensitive, so a `C` erased is not a `&C`.
test_verify_one_file! {
    #[test] dyn_any_is_decoration_sensitive verus_code! {
        use vstd::prelude::*;
        use core::any::Any;
        struct C(u64);
        fn test(c: &C) -> (r: bool)
            ensures !r,
        {
            let d: &dyn Any = c;
            d.is::<&C>()
        }
    } => Ok(())
}

// The shape this exists for: `Any` as a supertrait, the upcast written where it
// is used, and the guard a downcast rests on -- verified, and tied to the type
// erased into the object rather than to anything hand-declared.
test_verify_one_file! {
    #[test] dyn_any_supertrait_downcast_guard verus_code! {
        use vstd::prelude::*;
        use core::any::Any;
        use verus_builtin::{type_id, type_id_of};
        unsafe trait AnyMeta: Any + Send + Sync {
            spec fn is_untyped_spec(&self) -> bool;
        }
        struct M1;
        unsafe impl AnyMeta for M1 { spec fn is_untyped_spec(&self) -> bool { true } }
        struct M2;
        unsafe impl AnyMeta for M2 { spec fn is_untyped_spec(&self) -> bool { false } }

        fn is_meta<M: AnyMeta>(meta: &dyn AnyMeta) -> (r: bool)
            ensures r == (type_id_of(meta) == type_id::<M>()),
        {
            (meta as &dyn Any).is::<M>()
        }

        fn end_to_end(m: &M1) -> (r: bool)
            ensures r,
        {
            let d: &dyn AnyMeta = m;
            is_meta::<M1>(d)
        }

        fn discriminates(m: &M1) -> (r: bool)
            ensures !r,
        {
            let d: &dyn AnyMeta = m;
            is_meta::<M2>(d)
        }
    } => Ok(())
}

// `dyn Any` being a legal type does not give it an identity of its own: the
// rejection from the `type_id` side still stands.
test_verify_one_file! {
    #[test] dyn_any_type_id_still_rejected verus_code! {
        use vstd::prelude::*;
        use core::any::Any;
        use verus_builtin::type_id;
        proof fn t() {
            let x = type_id::<dyn Any>();
        }
    } => Err(err) => assert_vir_error_msg(err, "does not support `type_id` of the trait object type")
}

// --- the downcast itself, not just its guard ---------------------------------
//
// `dyn_value` is what lets a postcondition name the value that comes back. The
// coercion is the identity on the value, so reading it back at the type it was
// written at returns it; at any other type the term is unconstrained, which is
// the asymmetry a downcast has -- the guard is what licenses the value.

test_verify_one_file! {
    #[test] dyn_value_roundtrip verus_code! {
        use vstd::prelude::*;
        use verus_builtin::dyn_value;
        trait Tr { spec fn s(&self) -> u64; }
        struct C(u64);
        impl Tr for C { spec fn s(&self) -> u64 { self.0 } }
        fn concrete(c: &C) {
            let d: &dyn Tr = c;
            assert(dyn_value::<C, _>(d) == *c);
        }
        fn generic<F: Tr>(v: &F) {
            let d: &dyn Tr = v;
            assert(dyn_value::<F, _>(d) == *v);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] dyn_value_wrong_type_says_nothing verus_code! {
        use vstd::prelude::*;
        use verus_builtin::dyn_value;
        trait Tr { spec fn s(&self) -> u64; }
        struct C(u64);
        struct D(u64);
        impl Tr for C { spec fn s(&self) -> u64 { self.0 } }
        impl Tr for D { spec fn s(&self) -> u64 { 0 } }
        fn test(c: &C) {
            let d: &dyn Tr = c;
            assert(dyn_value::<D, _>(d) == D(c.0)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// `dyn_value` is about trait objects; a sized type has nothing erased to read.
test_verify_one_file! {
    #[test] dyn_value_requires_a_dyn_type verus_code! {
        use vstd::prelude::*;
        use verus_builtin::dyn_value;
        struct C(u64);
        proof fn test(c: &C) {
            let x = dyn_value::<C, _>(c);
        }
    } => Err(err) => assert_vir_error_msg(err, "must have a `dyn` type")
}

// A whole downcast: the guard proves the `None` arm unreachable, and the value
// that comes back is the one that was erased.
test_verify_one_file! {
    #[test] dyn_any_downcast_ref verus_code! {
        use vstd::prelude::*;
        use core::any::Any;
        struct C(u64);
        struct D(u64);
        fn downcast(c: &C) -> (r: u64)
            ensures r == c.0,
        {
            let d: &dyn Any = c;
            match d.downcast_ref::<C>() {
                Some(back) => back.0,
                None => {
                    assert(false);
                    0
                }
            }
        }
        fn refuses(c: &C) -> (r: bool)
            ensures !r,
        {
            let d: &dyn Any = c;
            d.downcast_ref::<D>().is_some()
        }
    } => Ok(())
}

// The owned form, including the retry a failed downcast is meant to allow.
test_verify_one_file! {
    #[test] dyn_any_downcast_boxed verus_code! {
        use vstd::prelude::*;
        use core::any::Any;
        struct C(u64);
        struct D(u64);
        fn owned(c: C) -> (r: u64)
            ensures r == c.0,
        {
            let b: Box<dyn Any> = Box::new(c);
            match b.downcast::<C>() {
                Ok(back) => (*back).0,
                Err(_) => { assert(false); 0 }
            }
        }
        fn retry(c: C) -> (r: u64)
            ensures r == c.0,
        {
            let b: Box<dyn Any> = Box::new(c);
            match b.downcast::<D>() {
                Ok(_) => { assert(false); 0 }
                Err(back) => match back.downcast::<C>() {
                    Ok(got) => (*got).0,
                    Err(_) => { assert(false); 0 }
                }
            }
        }
    } => Ok(())
}
