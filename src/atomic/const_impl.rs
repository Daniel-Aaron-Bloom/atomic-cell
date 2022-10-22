#![cfg(feature = "const")]

use super::FromInner;
use crate::cell::generic::{StorageMarker, UnderlyingMarker};

/// An abstraction to deal with the `const`ness of `AtomicStorage`
pub trait AtomicStorageBase: Sized {
    /// The underlying non-atomic type. Typically this should have the same in-memory
    /// representation as `Self`.
    type Underlying: Copy + PartialEq + ~const Into<Self> + ~const FromInner<Self>;
}

macro_rules! impl_storage_inner {
    (<$($g:ident)?> $t1:ty, $t2:ty, $z:expr) => {
impl $(<$g>)? const FromInner<$t1> for $t2 {
    fn from_inner(v: $t1) -> Self {
        v.into_inner()
    }
}
    }
}

impl<A, V: ~const Into<A> + Copy> const From<UnderlyingMarker<V>> for StorageMarker<A> {
    fn from(v: UnderlyingMarker<V>) -> Self {
        StorageMarker::new(v.into_inner().into())
    }
}

impl<A, U: ~const FromInner<A>> const FromInner<StorageMarker<A>> for UnderlyingMarker<U> {
    fn from_inner(v: StorageMarker<A>) -> Self {
        UnderlyingMarker::new(U::from_inner(v.into_inner()))
    }
}
