use crate::index::{IndexType, NodeIndex};
use crate::interval::Interval;
use crate::intervalmap::IntervalMap;
use crate::node::Node;

/// A view into a single entry in a map, which may either be vacant or occupied.
#[derive(Debug)]
pub enum Entry<'a, T, V, Ix>
where
    T: Ord,
{
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, T, V, Ix>),
    /// A vacant entry.
    Vacant(VacantEntry<'a, T, V, Ix>),
}

/// A view into an occupied entry in a `IntervalMap`.
/// It is part of the [`Entry`] enum.
#[derive(Debug)]
pub struct OccupiedEntry<'a, T, V, Ix>
where
    T: Ord,
{
    /// Reference to the map
    pub map_ref: &'a mut IntervalMap<T, V, Ix>,
    /// The entry node
    pub node_idx: NodeIndex<Ix>,
}

/// A view into a vacant entry in a `IntervalMap`.
/// It is part of the [`Entry`] enum.
#[derive(Debug)]
pub struct VacantEntry<'a, T, V, Ix>
where
    T: Ord,
{
    /// Mutable reference to the map
    pub map_ref: &'a mut IntervalMap<T, V, Ix>,
    /// The interval of this entry
    pub interval: Interval<T>,
}

impl<'a, T, V, Ix> Entry<'a, T, V, Ix>
where
    T: Ord,
    Ix: IndexType,
{
    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// a mutable reference to the value in the entry.
    ///
    /// # Example
    /// ```rust
    /// use interval_map::{Interval, IntervalMap, Entry};
    ///
    /// let mut map = IntervalMap::new();
    /// assert!(matches!(map.entry(Interval::new(1, 2)), Entry::Vacant(_)));
    /// map.entry(Interval::new(1, 2)).or_insert(3);
    /// assert!(matches!(map.entry(Interval::new(1, 2)), Entry::Occupied(_)));
    /// assert_eq!(map.get(&Interval::new(1, 2)), Some(&3));
    /// ```
    #[inline]
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.map_ref.node_mut(entry.node_idx, Node::value_mut),
            Entry::Vacant(entry) => {
                let entry_idx = NodeIndex::new(entry.map_ref.nodes.len());
                let _ignore = entry.map_ref.insert(entry.interval, default);
                entry.map_ref.node_mut(entry_idx, Node::value_mut)
            }
        }
    }

    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the map.
    ///
    /// # Panics
    ///
    /// This method panics when the node is a sentinel node
    ///
    /// # Example
    /// ```rust
    /// use interval_map::{Interval, IntervalMap, Entry};
    ///
    /// let mut map = IntervalMap::new();
    ///
    /// map.insert(Interval::new(6, 7), 3);
    /// assert!(matches!(map.entry(Interval::new(6, 7)), Entry::Occupied(_)));
    /// map.entry(Interval::new(6, 7)).and_modify(|v| *v += 1);
    /// assert_eq!(map.get(&Interval::new(6, 7)), Some(&4));
    /// ```
    #[inline]
    #[must_use]
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Entry::Occupied(entry) => {
                f(entry.map_ref.node_mut(entry.node_idx, Node::value_mut));
                Self::Occupied(entry)
            }
            Entry::Vacant(entry) => Self::Vacant(entry),
        }
    }
}
