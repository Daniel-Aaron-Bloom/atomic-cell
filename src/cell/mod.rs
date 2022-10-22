use core::{
    marker::PhantomData,
    mem::{align_of, replace, size_of, ManuallyDrop},
};

use const_panic::concat_assert;

use crate::{atomic::AtomicStorage, utils::destructure};

pub mod generic;
pub mod macros;

#[doc(hidden)]
pub union TransmuteUnderlying<T, A: AtomicStorage> {
    value: ManuallyDrop<T>,
    underlying: A::Underlying,
}

impl<T: Copy, A: AtomicStorage> Clone for TransmuteUnderlying<T, A> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: Copy, A: AtomicStorage> Copy for TransmuteUnderlying<T, A> {}

impl<T, A: AtomicStorage> TransmuteUnderlying<T, A> {
    const SIZE: usize = size_of::<Self>();
    const UNDERLYING_SIZE: usize = size_of::<A::Underlying>();
    const SIZE_MATCHES: bool = Self::SIZE == Self::UNDERLYING_SIZE;

    const ALIGN: usize = align_of::<TransmuteUnderlying<T, A>>();
    const UNDERLYING_ALIGN: usize = align_of::<A::Underlying>();
    /// This is true if all references to `A::Underlying` are safely
    /// transmutable to a `TransmuteUnderlying<T, A>`.
    const ALIGN_MATCHES: bool = Self::ALIGN % Self::UNDERLYING_ALIGN == 0;

    const fn assert_size_matches() {
        concat_assert!(
            <TransmuteUnderlying<T, A>>::SIZE_MATCHES,
            "type ",
            type_name::<T>("T"),
            " (size=",
            <TransmuteUnderlying<T, A>>::SIZE,
            ") overflowed storage ",
            type_name::<A>("A"),
            " (size=",
            <TransmuteUnderlying<T, A>>::UNDERLYING_SIZE,
            ")",
        );
    }

    const fn assert_align_matches() {
        Self::assert_size_matches();
        concat_assert!(
            <TransmuteUnderlying<T, A>>::ALIGN_MATCHES,
            "type ",
            type_name::<T>("T"),
            " (align=",
            <TransmuteUnderlying<T, A>>::ALIGN,
            ") overflowed storage ",
            type_name::<A>("A"),
            " (align=",
            <TransmuteUnderlying<T, A>>::UNDERLYING_ALIGN,
            ")",
        );
    }

    pub const fn from_value(val: T) -> Self {
        Self::assert_size_matches();
        // "zero" out the memory, this is done so that when smaller `T`s
        // are stored in larger `A`s, the unused bits have a consistent value
        let mut v = TransmuteUnderlying {
            underlying: A::ZERO,
        };
        v.value = ManuallyDrop::new(val);
        v
    }
    pub const fn from_underlying(val: A::Underlying) -> Self {
        Self::assert_size_matches();
        TransmuteUnderlying { underlying: val }
    }
    /// This is only safe to call when `self` was constructed from a proper `T` value
    pub const unsafe fn value(self) -> T {
        Self::assert_size_matches();
        ManuallyDrop::into_inner(self.value)
    }
    pub const fn underlying(&self) -> A::Underlying {
        Self::assert_size_matches();
        // This is safe because `A::Underlying` is `Copy`
        // so we're just returning some POD
        unsafe { self.underlying }
    }
    pub const fn into_underlying(self) -> A::Underlying {
        Self::assert_size_matches();
        // This is safe because `A::Underlying` is `Copy`
        // so we're just returning some POD
        unsafe { self.underlying }
    }
}

impl<T, A: AtomicStorage> TransmuteUnderlying<T, A> {
    pub fn from_mut(v: &mut A::Underlying) -> &mut Self {
        Self::assert_align_matches();
        // This is safe because the size alignment of `Self` and `A::Underlying` match
        unsafe { &mut *(v as *mut A::Underlying as *mut Self) }
    }

    /// This is only safe to call when `self` was constructed from a proper `T` value
    pub unsafe fn get_mut_value(&mut self) -> &mut T {
        Self::assert_size_matches();
        &mut self.value
    }
}

#[doc(hidden)]
#[inline]
pub const fn into_underlying<T, A: AtomicStorage>(val: T) -> A::Underlying {
    TransmuteUnderlying::<T, A>::from_value(val).into_underlying()
}

#[inline]
/// This is only safe to call when `self` was constructed from a proper `T` value
pub const unsafe fn from_underlying<T, A: AtomicStorage>(val: A::Underlying) -> T {
    TransmuteUnderlying::<T, A>::from_underlying(val).value()
}

const fn type_name<T>(_fallback: &'static str) -> &'static str {
    #[cfg(feature = "const")]
    let _fallback = core::any::type_name::<T>();
    _fallback
}

/// A thread-safe mutable memory location.
///
/// This type is equivalent to [`Cell`], except it can also be shared among
/// multiple threads.
///
/// Operations on `AtomicCell`s use atomic instructions with [`Acquire`]
/// ordering for loads and [`Release`] ordering for stores. Choice of `A`
/// selects what atomic storage and instructions are used.
///
/// [`Cell`]: core::cell::Cell
/// [`Acquire`]: core::sync::atomic::Ordering::Acquire
/// [`Release`]: core::sync::atomic::Ordering::Release
///
/// # Drop
///
/// `A::drop` is frequently avoided, instead [`AtomicStorage::into_inner`] is often
/// called. When a `AtomicCell` is dropped,  [`AtomicStorage::forgettable`] is called,
/// and then inner `T` value is extracted before `T::drop` is called.
///
/// # Panics
///
/// All functions will panic if `T` cannot be supported by `A`.
#[repr(transparent)]
pub struct AtomicCell<T, A: AtomicStorage> {
    /// While alive, `atomic` always holds a proper `T` value
    /// While being dropped, `atomic` always holds `A::forgettable()`
    atomic: ManuallyDrop<A>,
    _marker: PhantomData<T>,
}

// Any common `const` impls can go here
impl<T, A: AtomicStorage> AtomicCell<T, A> {
    const fn from_storage(atomic: A) -> Self {
        Self {
            atomic: ManuallyDrop::new(atomic),
            _marker: PhantomData,
        }
    }
    const fn into_storage(self) -> A {
        // This is safe because `AtomicCell` is #[repr(transparent)]
        unsafe { destructure(self) }
    }

    /// `true` if the storage can support storing `T`.
    pub const SUPPORTED: bool = <TransmuteUnderlying<T, A>>::SIZE_MATCHES;

    /// Tries to panic at compile-time if `!SUPPORTED`
    pub const ASSERT_SUPPORTED: () = Self::assert_size_matches();

    /// `true` if the refences to `A::Underlying` is properly aligned with `T`, such that reference can be transmuted.
    pub const REF_SUPPORTED: bool = Self::SUPPORTED && <TransmuteUnderlying<T, A>>::ALIGN_MATCHES;

    /// Tries to panic at compile-time if `!REF_SUPPORTED`
    pub const ASSERT_REF_SUPPORTED: () = Self::assert_align_matches();

    const fn assert_size_matches() {
        <TransmuteUnderlying<T, A>>::assert_size_matches();
    }

    const fn assert_align_matches() {
        <TransmuteUnderlying<T, A>>::assert_align_matches();
    }
}

impl<T, A: AtomicStorage> Drop for AtomicCell<T, A> {
    fn drop(&mut self) {
        let val = ManuallyDrop::into_inner(replace(
            &mut self.atomic,
            ManuallyDrop::new(A::forgettable()),
        ));
        let val = val.into_inner();
        let val = unsafe { from_underlying::<T, A>(val) };
        drop(val)
    }
}

unsafe impl<T: Send, A: AtomicStorage> Send for AtomicCell<T, A> {}
unsafe impl<T: Send, A: AtomicStorage> Sync for AtomicCell<T, A> {}
