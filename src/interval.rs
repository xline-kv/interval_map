//! The `Interval` stored in `IntervalMap` and represents the interval [low, high)
//!
//! `interval_map` supports `insert`, `delete`, and `iter` fns. Traversal is performed in the order of `Interval<T>` . For instance, with intervals of type `Interval<u32>`:
//! - [1,4)<[2,5), because 1<2
//! - [1,4)<[1,5), because 4<5
//!
//! So the order of intervals in `IntervalMap` is [1,4)<[1,5)<[2,5).
//!
//! Currently, `interval_map` only supports half-open intervals, i.e., [...,...).

/// The interval stored in `IntervalMap` represents [low, high)
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub struct Interval<T> {
    /// Low value
    pub low: T,
    /// high value
    pub high: T,
}

impl<T: Ord> Interval<T> {
    /// Create a new `Interval`
    ///
    /// # Panics
    ///
    /// This method panics when low >= high
    #[inline]
    pub fn new(low: T, high: T) -> Self {
        assert!(low < high, "invalid range");
        Self { low, high }
    }

    /// Checks if self overlaps with other interval
    #[inline]
    pub fn overlap(&self, other: &Self) -> bool {
        self.high > other.low && other.high > self.low
    }
}

/// Reference type of `Interval`
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IntervalRef<'a, T> {
    /// Low value
    low: &'a T,
    /// high value
    high: &'a T,
}

impl<'a, T: Ord> IntervalRef<'a, T> {
    /// Create a new `IntervalRef`
    ///
    /// # Panics
    ///
    /// This method panics when low >= high
    #[inline]
    pub fn new(low: &'a T, high: &'a T) -> Self {
        assert!(low < high, "invalid range");
        Self { low, high }
    }

    /// Check if self overlaps with a `Interval<T>`
    pub fn overlap(&self, other: &Interval<T>) -> bool {
        self.high > &other.low && &other.high > self.low
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    #[should_panic(expected = "invalid range")]
    fn invalid_range_should_panic() {
        let _interval = Interval::new(3, 1);
    }
}
