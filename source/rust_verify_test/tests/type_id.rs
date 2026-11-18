#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] distinct_primitive_constructors verus_code! {
        use verus_builtin::type_id;
        proof fn t() {
            assert(type_id::<u8>() != type_id::<u16>());
            assert(type_id::<bool>() != type_id::<u8>());
            assert(type_id::<int>() != type_id::<nat>());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] distinct_datatypes verus_code! {
        use verus_builtin::type_id;
        struct A;
        struct B;
        proof fn t() {
            assert(type_id::<A>() != type_id::<B>());
            assert(type_id::<A>() != type_id::<bool>());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] distinct_instantiations verus_code! {
        use verus_builtin::type_id;
        struct Wrap<T>(T);
        proof fn t() {
            assert(type_id::<Wrap<u8>>() != type_id::<Wrap<u16>>());
            assert(type_id::<Wrap<bool>>() != type_id::<Wrap<u8>>());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] argument_order_matters verus_code! {
        use verus_builtin::type_id;
        struct Pair<A, B>(A, B);
        proof fn t() {
            assert(type_id::<Pair<bool, u8>>() != type_id::<Pair<u8, bool>>());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] nested_and_recursive verus_code! {
        use vstd::prelude::*;
        use verus_builtin::type_id;
        struct Wrap<T>(T);
        enum List<T> { Nil, Cons(T, Box<List<T>>) }
        proof fn t() {
            assert(type_id::<Wrap<Wrap<u8>>>() != type_id::<Wrap<u8>>());
            assert(type_id::<List<u8>>() != type_id::<List<bool>>());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] const_generics verus_code! {
        use verus_builtin::type_id;
        struct Slab<const N: usize>;
        proof fn t() {
            assert(type_id::<Slab<64>>() != type_id::<Slab<128>>());
            assert(type_id::<[u8; 4]>() != type_id::<[u8; 8]>());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] reflexive verus_code! {
        use verus_builtin::type_id;
        struct Wrap<T>(T);
        proof fn t() {
            assert(type_id::<Wrap<u8>>() == type_id::<Wrap<u8>>());
        }
    } => Ok(())
}

// A TypeId is an ordinary ghost value: it can be stored, passed and compared.
test_verify_one_file! {
    #[test] storable verus_code! {
        use verus_builtin::type_id;
        use core::any::TypeId;
        struct Wrap<T>(T);
        proof fn t(x: TypeId) {
            let s = Wrap(x);
            assert(s.0 == x);
        }
        spec fn is_u8(x: TypeId) -> bool { x == type_id::<u8>() }
        proof fn u() {
            assert(is_u8(type_id::<u8>()));
        }
    } => Ok(())
}

// --- Soundness controls: these must NOT be provable ------------------------

test_verify_one_file! {
    #[test] type_params_not_distinct verus_code! {
        use verus_builtin::type_id;
        proof fn t<A, B>() {
            assert(type_id::<A>() != type_id::<B>()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] type_params_not_distinct_nested verus_code! {
        use verus_builtin::type_id;
        struct Wrap<T>(T);
        proof fn t<A, B>() {
            assert(type_id::<Wrap<A>>() != type_id::<Wrap<B>>()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] decoration_is_part_of_identity verus_code! {
        use vstd::prelude::*;
        use verus_builtin::type_id;
        use std::rc::Rc;
        use std::sync::Arc;
        struct S(u8);
        proof fn t() {
            assert(type_id::<&u8>()    != type_id::<u8>());
            assert(type_id::<&mut S>() != type_id::<S>());
            assert(type_id::<Box<S>>() != type_id::<S>());
            assert(type_id::<Rc<S>>()  != type_id::<S>());
            assert(type_id::<Arc<S>>() != type_id::<S>());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] decorations_distinguish_each_other verus_code! {
        use vstd::prelude::*;
        use verus_builtin::type_id;
        use std::rc::Rc;
        struct S(u8);
        proof fn t() {
            assert(type_id::<Box<S>>() != type_id::<Rc<S>>());
            assert(type_id::<&S>()     != type_id::<Box<S>>());
            assert(type_id::<&&S>()    != type_id::<&S>());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] parameter_decorations_are_folded verus_code! {
        use vstd::prelude::*;
        use verus_builtin::type_id;
        struct Wrap<T>(T);
        struct S(u8);
        proof fn t() {
            assert(type_id::<Wrap<&u8>>()    != type_id::<Wrap<u8>>());
            assert(type_id::<Wrap<Box<S>>>() != type_id::<Wrap<S>>());
        }
    } => Ok(())
}

// Decorating an opaque parameter is still distinguishing, because no
// instantiation of `A` can equal `&A` -- that would be an infinite type. This is
// a consequence of the datatype encoding's acyclicity, not an extra axiom.
test_verify_one_file! {
    #[test] decorated_type_param_is_distinct verus_code! {
        use verus_builtin::type_id;
        proof fn t<A>() {
            assert(type_id::<&A>() != type_id::<A>());
        }
    } => Ok(())
}

// ... but two *different* parameters stay indistinguishable even decorated: `A`
// and `B` may be instantiated equally, and so may `&A` and `&B`.
test_verify_one_file! {
    #[test] decorated_type_params_not_distinct verus_code! {
        use verus_builtin::type_id;
        proof fn t<A, B>() {
            assert(type_id::<&A>() != type_id::<&B>()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// An unresolved associated type is opaque, like a type parameter.
test_verify_one_file! {
    #[test] projections_not_distinct verus_code! {
        use verus_builtin::type_id;
        trait Tr { type Out; }
        proof fn t<A: Tr, B: Tr>() {
            assert(type_id::<A::Out>() != type_id::<B::Out>()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// --- `dyn` types are rejected, not silently indistinguishable ---------------
//
// Verus models a trait object type by its trait path and type arguments, which
// cannot tell `dyn A` from `dyn B`; neither the equality nor the disequality of
// their tags is provable. The error names that at the call site rather than
// leaving an unexplained failure wherever the identity is compared. The
// identity of what is *inside* a trait object is a separate question and is the
// one a downcast needs.

test_verify_one_file! {
    #[test] dyn_type_id_rejected verus_code! {
        use verus_builtin::type_id;
        trait A { spec fn a(&self) -> u64; }
        proof fn t() {
            let x = type_id::<dyn A>();
        }
    } => Err(err) => assert_vir_error_msg(err, "does not support `type_id` of the trait object type")
}

// A tag folds in the tags of its arguments, so a `dyn` type anywhere in the
// type is just as indistinguishable as one at the top.
test_verify_one_file! {
    #[test] dyn_type_id_rejected_under_decoration verus_code! {
        use vstd::prelude::*;
        use verus_builtin::type_id;
        trait A { spec fn a(&self) -> u64; }
        proof fn t() {
            let x = type_id::<Box<dyn A>>();
        }
    } => Err(err) => assert_vir_error_msg(err, "does not support `type_id` of the trait object type")
}

test_verify_one_file! {
    #[test] dyn_type_id_rejected_in_datatype_arg verus_code! {
        use vstd::prelude::*;
        use verus_builtin::type_id;
        trait A { spec fn a(&self) -> u64; }
        struct Wrap<T: ?Sized>(core::marker::PhantomData<T>);
        proof fn t() {
            let x = type_id::<Wrap<dyn A>>();
        }
    } => Err(err) => assert_vir_error_msg(err, "does not support `type_id` of the trait object type")
}

// A `?Sized` type parameter is not a `dyn` type: generic code that takes the
// identity of its parameter still works, which is what `vstd_extra`'s tagged
// storage relies on.
test_verify_one_file! {
    #[test] unsized_type_param_still_allowed verus_code! {
        use verus_builtin::type_id;
        proof fn t<T: ?Sized>() {
            assert(type_id::<T>() == type_id::<T>());
        }
        proof fn u<T: ?Sized>() {
            assert(type_id::<&T>() != type_id::<T>());
        }
    } => Ok(())
}

// --- `type_id_of`: the identity of the type a value actually has -------------
//
// A1: for a sized static type the value-level and type-level identities
// coincide, since a sized type admits no erasure.

test_verify_one_file! {
    #[test] type_id_of_sized verus_code! {
        use verus_builtin::{type_id, type_id_of};
        struct C(u64);
        proof fn concrete(x: &C) {
            assert(type_id_of(x) == type_id::<C>());
        }
        proof fn generic<T>(x: &T) {
            assert(type_id_of(x) == type_id::<T>());
        }
    } => Ok(())
}

// A1's guard is load-bearing: a `?Sized` parameter may be a trait object, whose
// value identity is the erased type's and not its own.
test_verify_one_file! {
    #[test] type_id_of_unsized_param_is_not_own_type verus_code! {
        use verus_builtin::{type_id, type_id_of};
        proof fn t<T: ?Sized>(x: &T) {
            assert(type_id_of(x) == type_id::<T>()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// A2: erasure is the identity on runtime type. The payoff is that this holds
// for a *type parameter*, which no per-impl fact can deliver -- it is what a
// client would otherwise simulate with a spec fn plus a per-impl obligation.
test_verify_one_file! {
    #[test] type_id_of_erased verus_code! {
        use verus_builtin::{type_id, type_id_of};
        trait Tr { spec fn s(&self) -> u64; }
        struct C(u64);
        impl Tr for C { spec fn s(&self) -> u64 { self.0 } }
        fn generic<F: Tr>(v: &F) {
            let d: &dyn Tr = v;
            assert(type_id_of(d) == type_id::<F>());
        }
        fn concrete(c: &C) {
            let d: &dyn Tr = c;
            assert(type_id_of(d) == type_id::<C>());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] type_id_of_erased_no_confusion verus_code! {
        use verus_builtin::{type_id, type_id_of};
        trait Tr { spec fn s(&self) -> u64; }
        struct C(u64);
        impl Tr for C { spec fn s(&self) -> u64 { self.0 } }
        fn test<F: Tr>(v: &F) {
            let d: &dyn Tr = v;
            assert(type_id_of(d) == type_id::<C>()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// A supertrait upcast lowers to a ToDyn whose Self *is* a trait object. A2
// recurses into it rather than concluding, so the erased identity propagates --
// concluding `type_id::<Self>()` there would be wrong, not merely weak.
test_verify_one_file! {
    #[test] type_id_of_upcast_propagates verus_code! {
        use verus_builtin::{type_id, type_id_of};
        trait A { spec fn a(&self) -> u64; }
        trait B: A { spec fn b(&self) -> u64; }
        struct C(u64);
        impl A for C { spec fn a(&self) -> u64 { 1 } }
        impl B for C { spec fn b(&self) -> u64 { 2 } }
        fn propagates(x: &dyn B) {
            let d: &dyn A = x;
            assert(type_id_of(d) == type_id_of(x));
        }
        fn end_to_end(c: &C) {
            let x: &dyn B = c;
            let d: &dyn A = x;
            assert(type_id_of(d) == type_id::<C>());
        }
    } => Ok(())
}

// Identity is decoration-sensitive, and `type_id_of` keys on the static type as
// well as the value, so a box is its own type rather than its content's.
test_verify_one_file! {
    #[test] type_id_of_decorations verus_code! {
        use vstd::prelude::*;
        use verus_builtin::{type_id, type_id_of};
        struct C(u64);
        fn boxed(b: &Box<C>) {
            assert(type_id_of(b) == type_id::<Box<C>>());
        }
        fn reference(r: &&C) {
            assert(type_id_of(r) == type_id::<&C>());
        }
    } => Ok(())
}

// Spec-only, with the diagnostic pointing at the executable counterpart.
test_verify_one_file! {
    #[test] type_id_of_exec_rejected verus_code! {
        use verus_builtin::type_id_of;
        struct C(u64);
        fn test(c: &C) -> bool {
            let x = type_id_of(c);
            true
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use")
}

// A dyn-compatible trait may state what its vtable already knows. The `Self`
// type argument of `type_id_of(self)` selects the receiver's own
// implementation, exactly as the dispatch argument of a receiver call does, so
// the contract survives the substitution of `dyn T` -- this is the shape an
// `Any`-style trait needs, and without it the trait would not be dyn compatible.
test_verify_one_file! {
    #[test] type_id_of_in_dyn_trait_spec verus_code! {
        use vstd::prelude::*;
        use verus_builtin::{type_id, type_id_of};
        use core::any::TypeId;
        trait Named {
            fn id(&self) -> (r: TypeId)
                ensures r == type_id_of(self);
        }
        struct C;
        impl Named for C {
            fn id(&self) -> (r: TypeId) { TypeId::of::<C>() }
        }
        fn through_vtable(x: &dyn Named) -> (r: TypeId)
            ensures r == type_id_of(x)
        { x.id() }
        fn erased(c: &C) {
            let d: &dyn Named = c;
            let r = d.id();
            assert(r == type_id::<C>());
        }
    } => Ok(())
}

// The permission is for the receiver only. This one is true of every concrete
// `Self` -- every value of one type shares that type's identity -- and false
// after substituting `dyn T`, where the quantifier ranges over every
// implementor's values. It is the hazard the check exists for, and it must stay
// rejected.
test_verify_one_file! {
    #[test] type_id_of_non_receiver_in_dyn_trait_spec verus_code! {
        use verus_builtin::type_id_of;
        use core::any::TypeId;
        trait Named {
            fn id(&self) -> (r: TypeId)
                ensures forall|b: &Self| #[trigger] type_id_of(b) == r;
        }
        fn test(x: &dyn Named) { }
    } => Err(err) => assert_vir_error_msg(err, "uses Self outside of the receiver")
}
