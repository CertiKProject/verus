#![allow(unused_imports)]

// `super::super::prelude`, not `crate::prelude`: this module is also compiled
// with `--is-core`, where `crate` is `core` and the absolute path does not exist.
use super::super::prelude::*;
use core::any::TypeId;

verus! {

/// Specifications for [`core::any::TypeId`].
pub assume_specification<T: ?Sized + 'static>[ TypeId::of::<T> ]() -> (r: TypeId)
    ensures
        r == type_id::<T>(),
;

pub assume_specification[ <TypeId as PartialEq<TypeId>>::eq ](x: &TypeId, y: &TypeId) -> (r: bool)
    ensures
        r == (*x == *y),
;

} // verus!
