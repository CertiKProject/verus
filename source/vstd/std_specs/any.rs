#![allow(unused_imports)]

use super::super::prelude::*;
use alloc::boxed::Box;
use core::alloc::Allocator;
use core::any::Any;
use core::any::TypeId;

verus! {

pub assume_specification<T: ?Sized + 'static>[ TypeId::of::<T> ]() -> (r: TypeId)
    ensures
        r == type_id::<T>(),
;

pub assume_specification[ <TypeId as PartialEq<TypeId>>::eq ](x: &TypeId, y: &TypeId) -> (r: bool)
    ensures
        r == (*x == *y),
;

/// `core::any::Any`, declared to Verus with **no methods**.
///
/// Declaring the trait is what makes `dyn Any` a legal type, which is what the
/// rest of this module needs. Declaring its `type_id` method would be unsound:
/// `core`'s blanket impl reads `TypeId::of::<Self>()`, and at `Self = dyn Any`
/// that is the trait object type's own identity rather than the erased type's --
/// rustc may pick either reading (rust#57893), so no postcondition is safe to
/// claim for it. The value-level question is `type_id_of`, a spec primitive, and
/// the executable answer comes out of the inherent methods below, which are
/// defined only on `dyn Any` and so have no such ambiguity.
///
/// With no methods and no associated types there is nothing for `core`'s
/// `?Sized` blanket impl and the object impl to disagree about, which is why
/// Verus accepts `dyn Any` despite the blanket impl.
#[verifier::external_trait_specification]
pub trait ExAny: 'static {
    type ExternalTraitSpecificationFor: Any;
}

/// `<dyn Any>::is::<T>()`.
///
/// The downcast guard: it holds exactly when the type erased into `x` is `T`.
/// Identity is decoration-sensitive, so this is false for `&T`, `Box<T>`,
/// `Rc<T>` and `Arc<T>` -- each has its own identity, at every level of
/// nesting. Rejecting is unconditionally sound; accepting rests on the
/// `TypeId` collision assumption the `PartialEq` specification above records.
pub assume_specification<T: Any>[ <dyn Any>::is::<T> ](x: &dyn Any) -> (r: bool)
    ensures
        r == (type_id_of(x) == type_id::<T>()),
;

/// `<dyn Any>::downcast_ref::<T>()`.
///
/// Two clauses, and the second is the one that makes the result usable: the
/// guard says *whether* the type matches, and `dyn_value` says *which value*
/// comes back, which is the value that was erased. Without it a caller holding
/// `Some(&T)` would know nothing about the `T`.
///
/// `dyn_value` is only constrained at the type that was erased, so the second
/// clause carries no information where the first is false -- which is the
/// asymmetry a downcast has: the guard is what licenses the value.
pub assume_specification<T: Any>[ <dyn Any>::downcast_ref::<T> ](x: &dyn Any) -> (r: Option<&T>)
    ensures
        r is Some <==> type_id_of(x) == type_id::<T>(),
        r is Some ==> r->Some_0 == dyn_value::<T, _>(x),
;

/// `Box<dyn Any>::downcast::<T>()`.
///
/// The owned counterpart: the same guard, the same value, and on failure the
/// box is handed back unchanged, which is what lets a caller try another type.
pub assume_specification<A: Allocator, T: Any>[ <Box<dyn Any, A>>::downcast::<T> ](
    x: Box<dyn Any, A>,
) -> (r: Result<Box<T, A>, Box<dyn Any, A>>)
    ensures
        r is Ok <==> type_id_of(&*x) == type_id::<T>(),
        r is Ok ==> *r->Ok_0 == dyn_value::<T, _>(&*x),
        r is Err ==> r->Err_0 == x,
;

} // verus!
