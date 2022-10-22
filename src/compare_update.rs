//! The [`CompareUpdate`] trait used for [`AtomicCell::compare_update_raw`]
//! 
//! [`AtomicCell::compare_update_raw`]: crate::AtomicCell::compare_update_raw

/// How to treat data across retries of [`AtomicCell::compare_update_raw`]
/// 
/// [`AtomicCell::compare_update_raw`]: crate::AtomicCell::compare_update_raw
pub trait CompareUpdate<Current, T> {
    /// The error type for [`CompareUpdate::retry`]s
    type Error;

    /// Backup data for retries
    type Retry;

    /// The final data returned
    type Final;

    /// Create the values for the first `compare_exchange_weak` and some backup data for retries.
    /// `U` is the assumed `current` value
    fn initial(self) -> (Self::Retry, Current, T);

    /// Try to create the data for the next iteration
    /// `current` is the value returned from the failed attempt to exchange
    /// `val` is the value which was failed to be stored by the previous iteration
    fn retry(retry: Self::Retry, current: Current, val: T)
        -> Result<(Self::Retry, T), Self::Error>;

    /// Combine the retry data and the swapped out value into the [`CompareUpdate::Final`] data.
    fn finalize(retry: Self::Retry, val: T) -> Self::Final;
}

impl<FI, U, T, F, C, E, FF, R> CompareUpdate<U, T> for (FI, F, FF)
where
    FI: FnOnce() -> (C, U, T),
    F: FnMut(C, U, T) -> Result<(C, T), E>,
    FF: FnOnce(C, T) -> R,
{
    type Error = E;
    type Retry = (C, F, FF);
    type Final = R;

    fn initial(self) -> (Self::Retry, U, T) {
        let (c, u, t) = self.0();
        ((c, self.1, self.2), u, t)
    }

    fn retry(
        (c, mut f, ff): Self::Retry,
        current: U,
        val: T,
    ) -> Result<(Self::Retry, T), Self::Error> {
        f(c, current, val).map(|(c, t)| ((c, f, ff), t))
    }

    fn finalize((c, _, ff): Self::Retry, val: T) -> Self::Final {
        ff(c, val)
    }
}

impl<FI, U, T, F, C, E> CompareUpdate<U, T> for (FI, F)
where
    FI: FnOnce() -> (C, U, T),
    F: FnMut(C, U, T) -> Result<(C, T), E>,
{
    type Error = E;
    type Retry = (C, F);
    type Final = T;

    fn initial(self) -> (Self::Retry, U, T) {
        let (c, u, t) = self.0();
        ((c, self.1), u, t)
    }

    fn retry((c, mut f): Self::Retry, current: U, val: T) -> Result<(Self::Retry, T), Self::Error> {
        f(c, current, val).map(|(c, t)| ((c, f), t))
    }

    fn finalize(_retry: Self::Retry, val: T) -> Self::Final {
        val
    }
}

impl<U, T, F, C, E> CompareUpdate<U, T> for (C, U, T, F)
where
    F: FnMut(C, U, T) -> Result<(C, T), E>,
{
    type Error = E;
    type Retry = (C, F);
    type Final = T;

    fn initial(self) -> (Self::Retry, U, T) {
        ((self.0, self.3), self.1, self.2)
    }

    fn retry((c, mut f): Self::Retry, current: U, val: T) -> Result<(Self::Retry, T), Self::Error> {
        f(c, current, val).map(|(c, t)| ((c, f), t))
    }

    fn finalize(_retry: Self::Retry, val: T) -> Self::Final {
        val
    }
}

impl<U, T, F, C, E, FF, R> CompareUpdate<U, T> for (C, U, T, F, FF)
where
    F: FnMut(C, U, T) -> Result<(C, T), E>,
    FF: FnOnce(C, T) -> R,
{
    type Error = E;
    type Retry = (C, F, FF);
    type Final = R;

    fn initial(self) -> (Self::Retry, U, T) {
        ((self.0, self.3, self.4), self.1, self.2)
    }

    fn retry(
        (c, mut f, ff): Self::Retry,
        current: U,
        val: T,
    ) -> Result<(Self::Retry, T), Self::Error> {
        f(c, current, val).map(|(c, t)| ((c, f, ff), t))
    }

    fn finalize((c, _, ff): Self::Retry, val: T) -> Self::Final {
        ff(c, val)
    }
}
