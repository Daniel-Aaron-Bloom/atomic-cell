//! The [`AtomicStorage`] trait and associated components
pub use core::sync::atomic::{
    AtomicBool, AtomicI16, AtomicI32, AtomicI64, AtomicI8, AtomicIsize, AtomicPtr, AtomicU16,
    AtomicU32, AtomicU64, AtomicU8, AtomicUsize, Ordering,
};

use Ordering::*;

use crate::cell::generic::{StorageMarker, UnderlyingMarker};
use crate::utils::maybe_const;

#[cfg(feature = "const")]
#[macro_use]
mod const_impl;
#[cfg(not(feature = "const"))]
#[macro_use]
mod non_const_impl;

#[cfg(feature = "const")]
pub use const_impl::*;
#[cfg(not(feature = "const"))]
pub use non_const_impl::*;

/// A `()` type which can be safely shared between threads.
///
/// This type has the same in-memory representation as a [`()`].
pub struct AtomicUnit {
    v: (),
}

maybe_const! {
impl const From<()> for AtomicUnit {
    fn from(v: ()) -> Self {
        Self { v }
    }
}
}

impl AtomicUnit {
    /// Creates a new `AtomicUnit`.
    pub const fn new(v: ()) -> Self {
        AtomicUnit { v }
    }

    /// Consumes the atomic and returns the contained value.
    ///
    /// This is safe because passing `self` by value guarantees that no other threads are
    /// concurrently accessing the atomic data.
    pub const fn into_inner(self) -> () {
        self.v
    }

    maybe_const! {
    /// Returns a mutable reference to the underlying [`()`].
    ///
    /// This is safe because the mutable reference guarantees that no other threads are
    /// concurrently accessing the atomic data.
    pub const fn get_mut(&mut self) -> &mut () {
        &mut self.v
    }
    }

    /// Loads a value from the bool.
    ///
    /// `load` takes an [`Ordering`] argument which describes the memory ordering
    /// of this operation. Possible values are [`SeqCst`], [`Acquire`] and [`Relaxed`].
    ///
    /// # Panics
    ///
    /// Panics if `order` is [`Release`] or [`AcqRel`].
    pub const fn load(&self, order: Ordering) -> () {
        match order {
            Release => panic!("there is no such thing as a release load"),
            AcqRel => panic!("there is no such thing as an acquire/release load"),
            _ => self.v,
        }
        self.v
    }

    /// Stores a value into the atomic.
    ///
    /// `store` takes an [`Ordering`] argument which describes the memory
    /// ordering of this operation. Possible values are [`SeqCst`],
    /// [`Release`] and [`Relaxed`].
    ///
    /// # Panics
    ///
    /// Panics if `order` is [`Acquire`] or [`AcqRel`].
    pub const fn store(&self, _val: (), order: Ordering) {
        match order {
            Acquire => panic!("there is no such thing as a release store"),
            AcqRel => panic!("there is no such thing as an acquire/release store"),
            _ => self.v,
        }
    }

    /// Stores a value into the atomic, returning the previous value.
    ///
    /// `swap` takes an [`Ordering`] argument which describes the memory
    /// ordering of this operation. All ordering modes are possible. Note
    /// that using [`Acquire`] makes the store part of this operation
    /// [`Relaxed`], and using [`Release`] makes the load part [`Relaxed`].
    pub const fn swap(&self, _val: (), _order: Ordering) -> () {}

    /// Stores a value into the atomic if the current value is the same as the
    /// `current` value.
    ///
    /// The return value is a result indicating whether the new value was written and containing
    /// the previous value. On success this value is guaranteed to be equal to `current`.
    ///
    /// `compare_exchange` takes two [`Ordering`] arguments to describe the
    /// memory ordering of this operation. `success` describes the required
    /// ordering for the read-modify-write operation that takes place if the
    /// comparison with `current` succeeds. `failure` describes the required
    /// ordering for the load operation that takes place when the comparison
    /// fails. Using [`Acquire`] as success ordering makes the store part of
    /// this operation [`Relaxed`], and using [`Release`] makes the successful
    /// load [`Relaxed`]. The failure ordering can only be [`SeqCst`],
    /// [`Acquire`] or [`Relaxed`] and must be equivalent to or weaker than
    /// the success ordering.
    pub const fn compare_exchange(
        &self,
        _current: (),
        _new: (),
        success: Ordering,
        failure: Ordering,
    ) -> Result<(), ()> {
        match (success, failure) {
            (_, AcqRel) => panic!("there is no such thing as an acquire/release failure ordering"),
            (_, Release) => panic!("there is no such thing as a release failure ordering"),
            (Relaxed, Relaxed)
            | (Acquire, Relaxed)
            | (Acquire, Acquire)
            | (Release, Relaxed)
            | (AcqRel, Relaxed)
            | (AcqRel, Acquire)
            | (SeqCst, _) => Ok(()),
            _ => panic!("a failure ordering can't be stronger than a success ordering"),
        }
    }

    /// Stores a value into the atomic if the current value is the same as the
    /// `current` value.
    ///
    /// Unlike [`AtomicUnit::compare_exchange`], This function is allowed to spuriously fail even when the comparison
    /// succeeds, which can result in more efficient code on some platforms. The
    /// return value is a result indicating whether the new value was written
    /// and containing the previous value.
    ///
    /// `compare_exchange_weak` takes two [`Ordering`] arguments to describe the
    /// memory ordering of this operation. `success` describes the required
    /// ordering for the read-modify-write operation that takes place if the
    /// comparison with `current` succeeds. `failure` describes the required
    /// ordering for the load operation that takes place when the comparison
    /// fails. Using [`Acquire`] as success ordering makes the store part of
    /// this operation [`Relaxed`], and using [`Release`] makes the successful
    /// load [`Relaxed`]. The failure ordering can only be [`SeqCst`],
    /// [`Acquire`] or [`Relaxed`] and must be equivalent to or weaker than
    /// the success ordering.
    pub const fn compare_exchange_weak(
        &self,
        _current: (),
        _new: (),
        success: Ordering,
        failure: Ordering,
    ) -> Result<(), ()> {
        match (success, failure) {
            (_, AcqRel) => panic!("there is no such thing as an acquire/release failure ordering"),
            (_, Release) => panic!("there is no such thing as a release failure ordering"),
            (Relaxed, Relaxed)
            | (Acquire, Relaxed)
            | (Acquire, Acquire)
            | (Release, Relaxed)
            | (AcqRel, Relaxed)
            | (AcqRel, Acquire)
            | (SeqCst, _) => Ok(()),
            _ => panic!("a failure ordering can't be stronger than a success ordering"),
        }
    }
}

/// A const wrapper for `into_inner`.
pub trait FromInner<A> {
    /// Consumes the atomic and returns the contained value.
    ///
    /// This is safe because passing `self` by value guarantees that no other threads are
    /// concurrently accessing the atomic data.
    fn from_inner(a: A) -> Self;
}

/// An atomic type which can be safely shared between threads. [`Drop::drop`] behavior is
/// somewhat unintuitive, so types are advised to avoid implementing it. See [`crate::cell::AtomicCell`]
/// for more info.
pub trait AtomicStorage: Sized + Send + Sync + AtomicStorageBase {
    /// An underlying value initialized to zero. (i.e. all values
    /// of `ZERO` should be [`PartialEq`] and equal according to
    /// [`AtomicStorage::compare_exchange_weak`]).
    const ZERO: Self::Underlying;

    /// Creates an atomic value which can be safely forgotten
    fn forgettable() -> Self {
        Self::new(Self::ZERO)
    }

    /// Creates a new `AtomicStorage` with the value `v`.
    fn new(v: Self::Underlying) -> Self;

    /// Consumes the atomic and returns the contained value.
    ///
    /// This is safe because passing `self` by value guarantees that no other threads are
    /// concurrently accessing the atomic data.
    fn into_inner(self) -> Self::Underlying;

    /// Returns a mutable reference to the underlying [`AtomicStorageBase::Underlying`].
    ///
    /// This is safe because the mutable reference guarantees that no other
    /// threads are concurrently accessing the atomic data.
    fn get_mut(&mut self) -> &mut Self::Underlying;

    // Loads a value from the atomic.
    ///
    /// `load` takes an [`Ordering`] argument which describes the memory
    /// ordering of this operation. Possible values are [`SeqCst`],
    /// [`Acquire`] and [`Relaxed`].
    ///
    /// # Panics
    ///
    /// Panics if `order` is [`Release`] or [`AcqRel`].
    fn load(&self, _order: Ordering) -> Self::Underlying;

    /// Stores a value into the atomic.
    ///
    /// `store` takes an [`Ordering`] argument which describes the memory
    /// ordering of this operation. Possible values are [`SeqCst`],
    /// [`Release`] and [`Relaxed`].
    ///
    /// # Panics
    ///
    /// Panics if `order` is [`Acquire`] or [`AcqRel`].
    fn store(&self, val: Self::Underlying, order: Ordering);

    /// Stores a value into the atomic, returning the previous value.
    ///
    /// `swap` takes an [`Ordering`] argument which describes the memory
    /// ordering of this operation. All ordering modes are possible. Note
    /// that using [`Acquire`] makes the store part of this operation
    /// [`Relaxed`], and using [`Release`] makes the load part [`Relaxed`].
    fn swap(&self, val: Self::Underlying, order: Ordering) -> Self::Underlying;

    /// Stores a value into the atomic if the current value is the same as the
    /// `current` value.
    ///
    /// The return value is a result indicating whether the new value was written and containing
    /// the previous value. On success this value is guaranteed to be equal to `current`.
    ///
    /// `compare_exchange` takes two [`Ordering`] arguments to describe the
    /// memory ordering of this operation. `success` describes the required
    /// ordering for the read-modify-write operation that takes place if the
    /// comparison with `current` succeeds. `failure` describes the required
    /// ordering for the load operation that takes place when the comparison
    /// fails. Using [`Acquire`] as success ordering makes the store part of
    /// this operation [`Relaxed`], and using [`Release`] makes the successful
    /// load [`Relaxed`]. The failure ordering can only be [`SeqCst`],
    /// [`Acquire`] or [`Relaxed`] and must be equivalent to or weaker than
    /// the success ordering.
    fn compare_exchange(
        &self,
        current: Self::Underlying,
        new: Self::Underlying,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Self::Underlying, Self::Underlying>;

    /// Stores a value into the atomic if the current value is the same as the
    /// `current` value.
    ///
    /// Unlike [`AtomicStorage::compare_exchange`], this function is allowed to spuriously fail even when the comparison
    /// succeeds, which can result in more efficient code on some platforms. The
    /// return value is a result indicating whether the new value was written
    /// and containing the previous value.
    ///
    /// `compare_exchange_weak` takes two [`Ordering`] arguments to describe the
    /// memory ordering of this operation. `success` describes the required
    /// ordering for the read-modify-write operation that takes place if the
    /// comparison with `current` succeeds. `failure` describes the required
    /// ordering for the load operation that takes place when the comparison
    /// fails. Using [`Acquire`] as success ordering makes the store part of
    /// this operation [`Relaxed`], and using [`Release`] makes the successful
    /// load [`Relaxed`]. The failure ordering can only be [`SeqCst`],
    /// [`Acquire`] or [`Relaxed`] and must be equivalent to or weaker than
    /// the success ordering.
    fn compare_exchange_weak(
        &self,
        current: Self::Underlying,
        new: Self::Underlying,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Self::Underlying, Self::Underlying>;
}

/// A wrapper around [`AtomicStorage::compare_exchange`] and [`AtomicStorage::compare_exchange_weak`]
pub fn compare_exchange<A: AtomicStorage, const WEAK: bool>(
    a: &A,
    current: A::Underlying,
    new: A::Underlying,
    success: Ordering,
    failure: Ordering,
) -> Result<A::Underlying, A::Underlying> {
    if WEAK {
        a.compare_exchange_weak(current, new, success, failure)
    } else {
        a.compare_exchange(current, new, success, failure)
    }
}

macro_rules! impl_storage {
    (<$($g:ident)?> $t1:ty, $t2:ty, $z:expr) => {
impl $(<$g>)? AtomicStorageBase for $t1 {
    type Underlying = $t2;
}

impl $(<$g>)? AtomicStorage for $t1 {
    const ZERO: Self::Underlying = $z as $t2;

    fn new(val: Self::Underlying) -> Self {
        <$t1>::new(val)
    }

    fn into_inner(self) -> Self::Underlying {
        <$t1>::into_inner(self)
    }

    fn get_mut(&mut self) -> &mut Self::Underlying {
        <$t1>::get_mut(self)
    }

    fn load(&self, order: Ordering) -> Self::Underlying {
        <$t1>::load(self, order)
    }

    fn store(&self, val: Self::Underlying, order: Ordering) {
        <$t1>::store(self, val, order)
    }

    fn swap(&self, val: Self::Underlying, order: Ordering) -> Self::Underlying {
        <$t1>::swap(self, val, order)
    }

    fn compare_exchange(
        &self,
        current: Self::Underlying,
        new: Self::Underlying,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Self::Underlying, Self::Underlying> {
        <$t1>::compare_exchange(self, current, new, success, failure)
    }

    fn compare_exchange_weak(
        &self,
        current: Self::Underlying,
        new: Self::Underlying,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Self::Underlying, Self::Underlying> {
        <$t1>::compare_exchange_weak(self, current, new, success, failure)
    }
}
impl_storage_inner!{<$($g)?> $t1, $t2, $z}
    };
    (<$($g:ident)?> $t1:ty, $t2:ty) => { impl_storage!{<$($g)?> $t1, $t2, 0} };
    ($t1:ty, $t2:ty, $z:expr) => { impl_storage!{<> $t1, $t2, $z} };
    ($t1:ty, $t2:ty) => { impl_storage!{<> $t1, $t2, 0} };
}

impl_storage! {<T> AtomicPtr<T>, *mut T, core::ptr::null_mut::<T>()}
impl_storage! {AtomicUsize, usize}
impl_storage! {AtomicIsize, isize}
impl_storage! {AtomicU64, u64}
impl_storage! {AtomicI64, i64}
impl_storage! {AtomicU32, u32}
impl_storage! {AtomicI32, i32}
impl_storage! {AtomicU16, u16}
impl_storage! {AtomicI16, i16}
impl_storage! {AtomicU8, u8}
impl_storage! {AtomicI8, i8}
impl_storage! {AtomicBool, bool, false}
impl_storage! {AtomicUnit, (), ()}

impl<A: AtomicStorageBase> AtomicStorageBase for StorageMarker<A> {
    type Underlying = UnderlyingMarker<A::Underlying>;
}

impl<A: AtomicStorage> AtomicStorage for StorageMarker<A> {
    const ZERO: Self::Underlying = UnderlyingMarker::new(A::ZERO);

    fn new(val: Self::Underlying) -> Self {
        StorageMarker::new(A::new(val.into_inner()))
    }

    fn into_inner(self) -> Self::Underlying {
        UnderlyingMarker::new(StorageMarker::into_inner(self).into_inner())
    }

    fn get_mut(&mut self) -> &mut Self::Underlying {
        UnderlyingMarker::as_mut((self as &mut A).get_mut())
    }

    fn load(&self, order: Ordering) -> Self::Underlying {
        UnderlyingMarker::new((self as &A).load(order))
    }

    fn store(&self, val: Self::Underlying, order: Ordering) {
        (self as &A).store(val.into_inner(), order)
    }

    fn swap(&self, val: Self::Underlying, order: Ordering) -> Self::Underlying {
        UnderlyingMarker::new((self as &A).swap(val.into_inner(), order))
    }

    fn compare_exchange(
        &self,
        current: Self::Underlying,
        new: Self::Underlying,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Self::Underlying, Self::Underlying> {
        (self as &A)
            .compare_exchange(current.into_inner(), new.into_inner(), success, failure)
            .map(UnderlyingMarker::new)
            .map_err(UnderlyingMarker::new)
    }

    fn compare_exchange_weak(
        &self,
        current: Self::Underlying,
        new: Self::Underlying,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Self::Underlying, Self::Underlying> {
        (self as &A)
            .compare_exchange_weak(current.into_inner(), new.into_inner(), success, failure)
            .map(UnderlyingMarker::new)
            .map_err(UnderlyingMarker::new)
    }
}
