//! The `Interval` stored in `IntervalMap` and represents the interval [low, high)
//!
//! `interval_map` supports `insert`, `delete`, and `iter` fns. Traversal is performed in the order of `Interval<T>` . For instance, with intervals of type `Interval<u32>`:
//! - [1,4)<[2,5), because 1<2
//! - [1,4)<[1,5), because 4<5
//!
//! So the order of intervals in `IntervalMap` is [1,4)<[1,5)<[2,5).
//!
//! Currently, `interval_map` only supports half-open intervals, i.e., [...,...).

use std::fmt::{Display, Formatter};

#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// The interval stored in `IntervalMap` represents [low, high)
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    pub fn overlaps(&self, other: &Self) -> bool {
        self.high > other.low && other.high > self.low
    }

    /// Checks if self contains other interval
    /// e.g. [1,10) contains [1,8)
    #[inline]
    pub fn contains(&self, other: &Self) -> bool {
        self.low <= other.low && self.high > other.high
    }

    /// Checks if self contains a point
    pub fn contains_point(&self, p: T) -> bool {
        self.low <= p && self.high > p
    }
}

impl<T: Display> Display for Interval<T> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "[{},{})", self.low, self.high)
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

#[cfg(feature = "serde")]
impl<T: Serialize> Serialize for Interval<T> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        (&self.low, &self.high).serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, T> Deserialize<'de> for Interval<T>
where
    T: Deserialize<'de>,
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let (low, high) = <(T, T)>::deserialize(deserializer)?;
        Ok(Interval { low, high })
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

    #[test]
    fn test_interval_clone() {
        let interval1 = Interval::new(1, 10);
        let interval2 = interval1.clone();
        assert_eq!(interval1, interval2);
    }

    #[test]
    fn test_interval_compare() {
        let interval1 = Interval::new(1, 10);
        let interval2 = Interval::new(5, 15);
        assert!(interval1 < interval2);
        assert!(interval2 > interval1);
        assert_eq!(interval1, Interval::new(1, 10));
        assert_ne!(interval1, interval2);
    }

    #[test]
    fn test_interval_hash() {
        let interval1 = Interval::new(1, 10);
        let interval2 = Interval::new(1, 10);
        let interval3 = Interval::new(5, 15);
        let mut hashset = std::collections::HashSet::new();
        hashset.insert(interval1);
        hashset.insert(interval2);
        hashset.insert(interval3);
        assert_eq!(hashset.len(), 2);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_interval_serialize_deserialize() {
        let interval = Interval::new(1, 10);
        let serialized = serde_json::to_string(&interval).unwrap();
        let deserialized: Interval<i32> = serde_json::from_str(&serialized).unwrap();
        assert_eq!(interval, deserialized);
    }
}
