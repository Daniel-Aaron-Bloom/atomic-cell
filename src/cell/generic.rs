//! An implementation of [`AtomicCell`] using generics to enable different [`AtomicStorage`] backends

use core::{
    fmt,
    mem::{needs_drop, transmute},
    ops::{Deref, DerefMut},
    sync::atomic::Ordering,
};

use crate::{
    atomic::{AtomicStorage, AtomicStorageBase, FromInner, compare_exchange},
    compare_update::CompareUpdate,
    utils::{destructure, maybe_const},
};

use super::{from_underlying, into_underlying, TransmuteUnderlying};

#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct StorageMarker<A>(A);

impl<A> StorageMarker<A> {
    pub const fn new(v: A) -> Self {
        Self(v)
    }
    pub const fn into_inner(self) -> A {
        // This is safe because `StorageMarker` is #[repr(transparent)]
        unsafe { destructure(self) }
    }
}

impl<A> Deref for StorageMarker<A> {
    type Target = A;
    fn deref(&self) -> &A {
        &self.0
    }
}
impl<A> DerefMut for StorageMarker<A> {
    fn deref_mut(&mut self) -> &mut A {
        &mut self.0
    }
}

#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct UnderlyingMarker<U>(U);

impl<U> Deref for UnderlyingMarker<U> {
    type Target = U;
    fn deref(&self) -> &U {
        &self.0
    }
}
impl<U> DerefMut for UnderlyingMarker<U> {
    fn deref_mut(&mut self) -> &mut U {
        &mut self.0
    }
}

impl<U> UnderlyingMarker<U> {
    pub const fn new(v: U) -> Self {
        Self(v)
    }
    pub const fn into_inner(self) -> U {
        // This is safe because `UnderlyingMarker` is #[repr(transparent)]
        unsafe { destructure(self) }
    }

    pub fn as_mut(a: &mut U) -> &mut Self {
        // This is safe because `UnderlyingMarker` is #[repr(transparent)]
        unsafe { transmute(a) }
    }
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
/// # Panics
///
/// All functions will panic if `T` cannot be supported by `A`.
pub type AtomicCell<T, A> = super::AtomicCell<UnderlyingMarker<T>, StorageMarker<A>>;

impl<T, A: AtomicStorage> AtomicCell<T, A> {
    maybe_const! {
        /// Creates a new atomic cell initialized with `val`.
        ///
        /// # Examples
        ///
        /// ```
        /// use atomic_cell::generic::AtomicCell;
        /// use std::sync::atomic::AtomicU32;
        ///
        /// let a = AtomicCell::<_, AtomicU32>::new(7);
        /// ```
        pub const fn new(val: T) -> Self {
            Self::assert_size_matches();
            let val = into_underlying::<T, A>(val);
            Self::from_storage(UnderlyingMarker::new(val).into())
        }
    }

    maybe_const! {
        /// Consumes the atomic and returns the contained value.
        ///
        /// # Examples
        ///
        /// ```
        /// use atomic_cell::generic::AtomicCell;
        /// use std::sync::atomic::AtomicU32;
        ///
        /// let a = AtomicCell::<_, AtomicU32>::new(7);
        /// let v = a.into_inner();
        ///
        /// assert_eq!(v, 7);
        /// ```
        pub const fn into_inner(self) -> T {
            Self::assert_size_matches();
            let val = UnderlyingMarker::<<A as AtomicStorageBase>::Underlying>::from_inner(self.into_storage());
            let val = val.into_inner();

            // This is safe because passing `self` by value guarantees ownership over `self.atomic`
            // from which `val` takes ownership of the proper `T` value
            unsafe { from_underlying::<T, A>(val) }
        }
    }

    /// Returns a mutable reference to contained data.
    ///
    /// This is safe because the mutable reference guarantees that no other
    /// threads are concurrently accessing the atomic data.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_cell::generic::AtomicCell;
    /// use std::num::NonZeroU32;
    /// use std::sync::atomic::AtomicU32;
    ///
    /// let mut a = AtomicCell::<_, AtomicU32>::new(NonZeroU32::new(7));
    /// assert_eq!(*a.get_mut(), NonZeroU32::new(7));
    /// *a.get_mut() = NonZeroU32::new(12);
    /// assert_eq!(a.load(), NonZeroU32::new(12));
    /// ```
    pub fn get_mut(&mut self) -> &mut T {
        Self::assert_align_matches();
        let v = TransmuteUnderlying::<T, A>::from_mut(self.atomic.get_mut());
        
        // This is safe because passing `self` by mutable reference guarantees ownership over `self.atomic`
        // which contains a proper `T` value.
        unsafe { v.get_mut_value() }
    }

    /// Stores `val` into the atomic cell.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_cell::generic::AtomicCell;
    /// use std::sync::atomic::AtomicU32;
    ///
    /// let a = AtomicCell::<_, AtomicU32>::new(7);
    ///
    /// assert_eq!(a.load(), 7);
    /// a.store(8);
    /// assert_eq!(a.load(), 8);
    /// ```
    pub fn store(&self, val: T) {
        Self::assert_size_matches();
        if needs_drop::<T>() {
            drop(self.swap(val));
        } else {
            let val = into_underlying::<T, A>(val);
            self.atomic
                .store(UnderlyingMarker::new(val), Ordering::Release);
        }
    }

    /// Load a raw value from the the atomic cell. These raw values are not
    /// guaranteed to be safe to transmute, but do have a guarantee of byte
    /// equivalency to a previously safe value been safe to transmute at one
    /// point. By the time these values are returned, they are no longer safe
    /// (e.g. if the value is a pointer, the memory pointed to may already be
    /// freed).
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_cell::generic::AtomicCell;
    /// use std::sync::atomic::AtomicU32;
    ///
    /// struct NoCopy(u32);
    ///
    /// let a = AtomicCell::<_, AtomicU32>::new(NoCopy(7));
    ///
    /// assert_eq!(a.load_raw(), 7);
    /// ```
    pub fn load_raw(&self) -> A::Underlying {
        Self::assert_size_matches();
        self.atomic.load(Ordering::Acquire).into_inner()
    }

    /// Stores `val` into the atomic cell and returns the previous value.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_cell::generic::AtomicCell;
    /// use std::sync::atomic::AtomicU32;
    ///
    /// let a = AtomicCell::<_, AtomicU32>::new(7);
    ///
    /// assert_eq!(a.load(), 7);
    /// assert_eq!(a.swap(8), 7);
    /// assert_eq!(a.load(), 8);
    /// ```
    pub fn swap(&self, val: T) -> T {
        Self::assert_size_matches();
        let val = into_underlying::<T, A>(val);
        let val = self
            .atomic
            .swap(UnderlyingMarker::new(val), Ordering::AcqRel);
        let val = val.into_inner();

        // This is safe because `val` is a proper `T` value which was swapped out of `self.atomic`,
        // and thus has guaranteed ownership.
        unsafe { from_underlying::<T, A>(val) }
    }

    /// Get a raw copy of a value (useful for `compare_update_raw`).
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_cell::generic::AtomicCell;
    /// use std::num::NonZeroU32;
    /// use std::sync::atomic::AtomicU32;
    ///
    /// assert_eq!(AtomicCell::<_, AtomicU32>::get_raw(7).1, 7);
    /// assert_eq!(
    ///     AtomicCell::<Option<NonZeroU32>, AtomicU32>::get_raw(None).1,
    ///     0
    /// );
    /// assert_eq!(
    ///     AtomicCell::<_, AtomicU32>::get_raw(NonZeroU32::new(5)).1,
    ///     5
    /// );
    /// ```
    pub fn get_raw(val: T) -> (T, A::Underlying) {
        let val = TransmuteUnderlying::<T, A>::from_value(val);
        let raw = val.underlying();

        // This is safe because `val` is an owned, proper `T` value.
        let val = unsafe { val.value() };
        (val, raw)
    }

    // Stores a value into the pointer if the current value is the same as the `current` value.
    ///
    /// The return value is a result indicating whether the new value was written. On success, this contains
    /// the previous value and is guaranteed to be equal to `current`. On failure, this contains `new` and the value currently stored in `Raw
    ///
    /// If `WEAK` is set, this function is allowed to spuriously fail even when the
    /// comparison succeeds, which can result in more efficient code on some platforms. The
    /// return value is a result indicating whether the new value was written and containing the
    /// previous value.
    pub fn compare_exchange_raw<const WEAK: bool>(&self, current: A::Underlying, new: T) -> Result<T, (T, A::Underlying)> {
        let new = TransmuteUnderlying::<T, A>::from_value(new);

        match compare_exchange::<A, WEAK>(&self.atomic,
            current,
            new.underlying(),
            Ordering::AcqRel,
            Ordering::Acquire,
        ) {
            
            // This is safe because `val` is a proper `T` value which was swapped out of `self.atomic`,
            // and thus has guaranteed ownership.
            Ok(val) => Ok(unsafe { from_underlying::<T, A>(val) }),
            // This is safe because `new` is an owned, proper `T` value.
            Err(next_curr) => Err((unsafe { new.value() }, next_curr)),
        }
    }

    /// Tries to swap out the value in the cell for one provided by
    /// [`CompareUpdate`].
    ///
    /// First, `updater.initial()` is called, and the returned value is attempted to be exchanged into the cell.
    /// If it fails for any reason (e.g. it has been changed from other threads in the
    /// meantime), `CompareUpdate::retry` will be called to enable updates to the to-be-stored value between attempts.
    /// `retry` may return `Err(_)` to signal that the update attempt should be aborted.
    ///
    /// When the attempt to store eventually succeeds, `CompareUpdate::finalize` will be called and the result returned.
    ///
    /// The `Current` type is `$a::Underlying`. There are no special restrictions on the raw values returned by `CompareUpdate::initial`.
    /// The raw value passed to `CompareUpdate::retry` is the most recently read raw value from the cell.
    /// These raw values are not guaranteed to be safe to transmute (unless T is `Copy`), but do
    /// have a guarantee of byte equivalency to a previously safe value been
    /// safe to transmute at one point. By the time these values are passed to
    /// `f`, they may no longer safe (e.g. if the value is a pointer, the
    /// memory pointed to may already be freed).
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_cell::AtomicCell;
    /// use std::sync::atomic::AtomicU32;
    ///
    /// let a = AtomicCell::<_, AtomicU32>::new(7);
    ///
    /// let v: Result<_, ()> = a.compare_update_raw::<_, true>((
    ///     (),      // No retry data
    ///     7,       // The expected current raw value
    ///     8,       // The initial value to try to swap in
    ///     |(), _raw, _val| Ok((
    ///         (),  // No retry data
    ///         14,  // Value to-be-swapped-in on retries
    ///     )),
    /// ));
    /// assert_eq!(v, Ok(7));    // The swapped value
    /// assert_eq!(a.load(), 8);
    ///
    /// let v = a.compare_update_raw::<_, true>((
    ///     "hello", // Arbitrary retry data
    ///     5,                              // Cell contains `8`, so passing `5` will result in at least 1 closure invocation
    ///     42,
    ///     |c, raw, _val| match (c, raw) {
    ///         // The cell contains an 8, not a 5, so now let's fail
    ///         ("hello", 8) => Err("arbitrary error"),
    ///         (c, v) => panic!("unexpected value ({}, {})", c, v),
    ///     },
    /// ));
    /// assert_eq!(v, Err("arbitrary error"));
    /// assert_eq!(a.load(), 8);
    /// ```
    ///
    /// `T::drop` can be avoided quite easily.
    ///
    /// ```
    /// use atomic_cell::AtomicCell;
    /// use std::mem::drop;
    /// use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering::Relaxed};
    ///
    /// static DROPPED: AtomicUsize = AtomicUsize::new(0);
    /// #[derive(Debug)]
    /// struct Dropper(u32);
    /// impl Drop for Dropper {
    ///     fn drop(&mut self) {
    ///         DROPPED.fetch_add(1, Relaxed);
    ///     }
    /// }
    ///
    /// let a = AtomicCell::<_, AtomicPtr<Dropper>>::new(Some(Box::new(Dropper(5))));
    /// let raw_none = AtomicCell::<Option<Box<Dropper>>, AtomicPtr<Dropper>>::get_raw(None).1;
    ///
    /// // Try (should fail) to swap out `None` while only allocating once
    /// let v = Some(Box::new(Dropper(6)));
    /// let v = a.compare_update_raw::<_, true>(((), raw_none, v, |(), raw: *mut Dropper, v| {
    ///     if raw == raw_none {
    ///         Ok(((), v))      // Keep trying with `v`
    ///     } else {
    ///         Err(v)           // Abort, saving the data
    ///     }
    /// }));
    ///
    /// // Retreive the allocation from the error
    /// let v = v.expect_err("compare_update_raw should have aborted");
    ///
    /// // Drop the value in the cell
    /// assert_eq!(DROPPED.load(Relaxed), 0);
    /// a.store(None);
    /// assert_eq!(DROPPED.load(Relaxed), 1);
    ///
    /// // Try to swap again, using the same allocation
    /// let v = a.compare_update_raw::<_, true>(((), raw_none, v, |(), raw, v| {
    ///     if raw == raw_none {
    ///         Ok(((), v))
    ///     } else {
    ///         Err(v)
    ///     }
    /// }));
    /// let v = v.expect("compare_update_raw should have succeeded");
    /// assert!(v.is_none());
    ///
    /// assert_eq!(DROPPED.load(Relaxed), 1);
    /// drop(a);
    /// assert_eq!(DROPPED.load(Relaxed), 2);
    /// ```
    pub fn compare_update_raw<C, const WEAK: bool>(&self, updater: C) -> Result<C::Final, C::Error>
    where
        C: CompareUpdate<A::Underlying, T>,
    {
        Self::assert_size_matches();
        let (mut retry, mut curr, mut val) = updater.initial();
        loop {
            match self.compare_exchange_raw::<WEAK>(
                curr,
                val,
            ) {
                Ok(prev) => return Ok(C::finalize(retry, prev)),
                Err((v, next_curr)) => {
                    let (c, v) = C::retry(retry, next_curr, v)?;
                    retry = c;
                    curr = next_curr;
                    val = v;
                }
            }
        }
    }
}

impl<T: Copy + fmt::Debug, A: AtomicStorage> fmt::Debug for AtomicCell<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.load().fmt(f)
    }
}

impl<T: Default, A: AtomicStorage> AtomicCell<T, A> {
    /// Takes the value of the atomic cell, leaving `Default::default()` in its
    /// place.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_cell::generic::AtomicCell;
    /// use std::sync::atomic::AtomicU32;
    ///
    /// let a = AtomicCell::<_, AtomicU32>::new(5);
    ///
    /// assert_eq!(a.take(), 5);
    /// assert_eq!(a.into_inner(), 0);
    /// ```
    pub fn take(&self) -> T {
        Self::assert_size_matches();
        self.swap(Default::default())
    }
}

impl<T: Copy, A: AtomicStorage> AtomicCell<T, A> {
    /// Load a value from the the atomic cell.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_cell::generic::AtomicCell;
    /// use std::sync::atomic::AtomicU32;
    ///
    /// let a = AtomicCell::<_, AtomicU32>::new(7);
    ///
    /// assert_eq!(a.load(), 7);
    /// ```
    pub fn load(&self) -> T {
        Self::assert_size_matches();
        let val = self.load_raw();
        
        // This is safe because `val` is a `Copy` of  `self.atomic` which contains a proper `T` value.
        unsafe { from_underlying::<T, A>(val) }
    }

    /// Tries to swap out the value in the cell for one provided by
    /// [`CompareUpdate`].
    /// 
    /// First, `updater.initial()` is called, and the returned value is attempted to be exchanged into the cell.
    /// If it fails for any reason (e.g. it has been changed from other threads in the
    /// meantime), `CompareUpdate::retry` will be called to enable updates to the to-be-stored value between attempts.
    /// `retry` may return `Err(_)` to signal that the update attempt should be aborted.
    /// 
    /// When the attempt to store eventually succeeds, `CompareUpdate::finalize` will be called and the result returned.
    ///
    /// The `Current` type is `T`. There are no special restrictions on the values returned by `CompareUpdate::initial`.
    /// The value passed to `CompareUpdate::retry` is the most recently read value from the cell.
    pub fn compare_update<C, const WEAK: bool>(&self, updater: C) -> Result<C::Final, C::Error>
    where
        C: CompareUpdate<T, T>,
    {
        Self::assert_size_matches();
        self.compare_update_raw::<_, WEAK>((
            || {
                let (retry, curr, val) = updater.initial();
                (retry, into_underlying::<T, A>(curr), val)
            },
            |retry, curr, val| {
                // This is safe because `curr` is a `Copy` of  `self.atomic` which contains a proper `T` value.
                let curr = unsafe { from_underlying::<T, A>(curr) };

                C::retry(retry, curr, val)
            },
            C::finalize
        ))
    }

    /// Fetches the value, and applies a function to it that returns an optional
    /// new value. Returns a `Result` of `Ok(previous_value)` if the function
    /// returned `Some(_)`, else `Err(previous_value)`.
    ///
    /// Note: This may call the function multiple times if the value has been
    /// changed from other threads in the meantime, as long as the function
    /// returns `Some(_)`, but the function will have been applied only once
    /// to the stored value.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_cell::macros::AtomicCell;
    /// use std::sync::atomic::AtomicU32;
    ///
    /// let a = AtomicCell::<_, AtomicU32>::new(7);
    ///
    /// assert_eq!(a.fetch_update::<_, true>(|_| None), Err(7));
    /// assert_eq!(a.fetch_update::<_, true>(|a| Some(a + 1)), Ok(7));
    /// assert_eq!(a.fetch_update::<_, true>(|a| Some(a + 1)), Ok(8));
    /// assert_eq!(a.load(), 9);
    /// ```
    pub fn fetch_update<F: FnMut(T) -> Option<T>, const WEAK: bool>(&self, mut f: F) -> Result<T, T> {
        Self::assert_size_matches();
        let curr = self.load();
        let val = match f(curr) {
            Some(val) => val,
            None => return Err(curr),
        };
        self.compare_update::<_, WEAK>(((), curr, val, |(), curr, _| match f(curr) {
            Some(val) => Ok(((), val)),
            None => Err(curr),
        }))
    }
}

impl<T: Copy + PartialEq, A: AtomicStorage> AtomicCell<T, A> {
    /// If the current value equals `current`, stores `new` into the atomic
    /// cell.
    ///
    /// The return value is a result indicating whether the new value was
    /// written and containing the previous value. On success this value is
    /// guaranteed to be equal to `current`.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_cell::generic::AtomicCell;
    /// use std::sync::atomic::AtomicU32;
    ///
    /// let a = AtomicCell::<_, AtomicU32>::new(1);
    ///
    /// assert_eq!(a.compare_exchange::<true>(2, 3), Err(1));
    /// assert_eq!(a.load(), 1);
    ///
    /// assert_eq!(a.compare_exchange::<true>(1, 2), Ok(1));
    /// assert_eq!(a.load(), 2);
    /// ```
    pub fn compare_exchange<const WEAK: bool>(&self, current: T, new: T) -> Result<T, T> {
        Self::assert_size_matches();
        self.compare_update::<_, WEAK>(((), current, new, |(), prev, new| {
            if current == prev {
                Ok(((), new))
            } else {
                Err(prev)
            }
        }))
    }
}
