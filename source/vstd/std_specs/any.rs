#![allow(unused_imports)]

// `super::super::prelude`, not `crate::prelude`: this module is also compiled
// with `--is-core`, where `crate` is `core` and the absolute path does not exist.
use super::super::prelude::*;
use core::any::TypeId;

verus! {

/// Specifications for [`core::any::TypeId`].
///
/// # These two are the trusted base for type identity
///
/// Together they say: a `TypeId` is a *unique* identifier for a type, and
/// comparing two of them decides type equality. That is what `core` documents --
/// *"a `TypeId` represents a globally unique identifier for a type"* -- and it is
/// what every downcast rests on.
///
/// It is not something `core` *proves*. `TypeId::of::<T>()` is
/// `intrinsics::type_id::<T>()`, a 128-bit hash of the type, so two distinct
/// types could in principle receive the same id. The chance is small. It is not
/// zero, and nothing here or in `core` rules it out.
///
/// # This is the *only* residual assumption
///
/// The spec-side tag adds none of its own. Constructor ids are a per-context
/// counter (`vir/src/def.rs`), injective by construction, so there is no
/// spec-side hash to collide -- unlike, say, string literals, where Verus does
/// take a SHA-512 no-collision assumption. Everything uncertain about type
/// identity is concentrated in the runtime hash, right here.
///
/// Hashing the path spec-side instead would not have helped: a path hash and
/// rustc's type-id hash are independent functions, so under a runtime collision
/// the path hashes still differ and the first specification below is falsified
/// exactly as it would be now. It would only add a second, likelier failure mode.
/// See the tag note in `vir/src/def.rs` for that argument and for the structural
/// invariant the counter costs instead.
///
/// # Why assuming it is not a weaker position than safe Rust
///
/// `core`'s own downcast is
///
/// ```text
/// if self.is::<T>() { unsafe { /* reinterpret as T */ } } else { None }
/// ```
///
/// which is sound *iff* `TypeId` is injective. So this is not an extra
/// assumption taken on to make verification go through -- it is the assumption
/// safe Rust's `Any` already makes. A collision unsounds `core::any` whether or
/// not Verus is involved.
///
/// The full argument, with the derivable steps machine-checked, is in
/// `vstd_extra::typing::soundness`.
pub assume_specification<T: ?Sized + 'static>[ TypeId::of::<T> ]() -> (r: TypeId)
    ensures
        r == type_id::<T>(),
;

/// Deciding identity at runtime.
///
/// Compares the raw bits of two 128-bit hashes; specified as deciding equality of
/// the modelled tags. Sound under the same assumption documented above.
pub assume_specification[ <TypeId as PartialEq<TypeId>>::eq ](x: &TypeId, y: &TypeId) -> (r: bool)
    ensures
        r == (*x == *y),
;

} // verus!
