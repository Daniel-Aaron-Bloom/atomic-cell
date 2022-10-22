#![cfg(not(feature = "const"))]

use super::{AtomicStorage, FromInner};
use crate::cell::generic::{StorageMarker, UnderlyingMarker};

/// An abstraction to deal with the `const`ness of `AtomicStorage`
pub trait AtomicStorageBase: Sized {
    /// The underlying non-atomic type. Typically this should have the same in-memory
    /// representation as `Self`.
    type Underlying: Copy + PartialEq + Into<Self>;
}

macro_rules! impl_storage_inner {
    (<$($g:ident)?> $t1:ty, $t2:ty, $z:expr) => {};
}

impl<U, A: AtomicStorage<Underlying = U>> FromInner<A> for U {
    fn from_inner(a: A) -> Self {
        a.into_inner()
    }
}

impl<A, V: Into<A>> From<UnderlyingMarker<V>> for StorageMarker<A> {
    fn from(v: UnderlyingMarker<V>) -> Self {
        StorageMarker::new(v.into_inner().into())
    }
}
