#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// `type_id::<T>()` yields the identity of `T`. Two of them are equal exactly when
// the tag axioms make the types equal; see vir::def's TYPE_TAG documentation.

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

// The case no user-level axiom can express: two instantiations of one constructor.
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

// The retirement: `type_id::<T>()` and `TypeId::of::<T>()` are one value of one
// type, so a runtime test establishes the spec fact with no `view()` between.
test_verify_one_file! {
    #[test] runtime_and_spec_id_are_one_value verus_code! {
        use vstd::prelude::*;
        use verus_builtin::type_id;
        use core::any::TypeId;

        fn decides() -> (r: bool)
            ensures r,
        {
            let a = TypeId::of::<u8>();
            let b = TypeId::of::<u16>();
            let c = TypeId::of::<u8>();
            assert(a == type_id::<u8>());
            !a.eq(&b) && a.eq(&c)
        }

        proof fn ghost_and_runtime_agree(g: TypeId)
            requires g == type_id::<u8>(),
            ensures  g != type_id::<Box<u8>>(),
        { }
    } => Ok(())
}

// --- Soundness controls: these must NOT be provable ------------------------

// A and B may be instantiated to the same type.
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

// Identity is decoration-*sensitive*, matching core::any::TypeId. The decoration
// spine is folded into the tag by `TYPE%tagd`, so a downcast guarded on a tag
// really does establish the type: without this, `&u8` and `u8` share an identity
// and `x.is::<&u8>()` succeeds for an erased `u8`.
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

// Distinct decorations are distinct from *each other*, not merely from the bare
// type, and the spine nests.
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

// The case a top-level-only fold would miss: a decoration on a type *argument*.
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

// type_id is spec-only.
test_verify_one_file! {
    #[test] not_usable_in_exec verus_code! {
        use verus_builtin::type_id;
        fn t() {
            let x = type_id::<u8>();
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use spec-mode expression in executable context")
}
