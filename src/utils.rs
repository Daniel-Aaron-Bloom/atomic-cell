use core::mem::ManuallyDrop;

#[cfg(feature = "const")]
macro_rules! maybe_const {
    ($( #[$attr:meta] )* $v:vis const $($i:tt)*) => { $( #[$attr] )* $v const $($i)* };
    (impl const $($i:tt)*) => { impl const $($i)* };
}

#[cfg(not(feature = "const"))]
macro_rules! maybe_const {
    ($( #[$attr:meta] )* $v:vis const $($i:tt)*) => { $( #[$attr] )* $v $($i)* };
    (impl const $($i:tt)*) => { impl $($i)* };
}

pub(crate) use maybe_const;

/// This function destructures `O` into `I` without calling `O::Drop`. The caller must guarantee
/// that `O` is a `#[repr(transparent)]` wrapper around `I`.
pub const unsafe fn destructure<O, I>(outer: O) -> I {
    union Transmute<M, U> {
        outer: ManuallyDrop<M>,
        inner: ManuallyDrop<U>,
    }
    let v = Transmute {
        outer: ManuallyDrop::new(outer),
    };
    ManuallyDrop::into_inner(v.inner)
}
