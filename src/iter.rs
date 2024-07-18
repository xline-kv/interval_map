use std::fmt::Debug;

use crate::index::{IndexType, NodeIndex};
use crate::interval::Interval;
use crate::intervalmap::IntervalMap;
use crate::node::Node;

/// Pushes a link of nodes on the left to stack.
fn left_link<T, V, Ix>(map_ref: &IntervalMap<T, V, Ix>, mut x: NodeIndex<Ix>) -> Vec<NodeIndex<Ix>>
where
    T: Ord,
    Ix: IndexType,
{
    let mut nodes = vec![];
    while !map_ref.node_ref(x, Node::is_sentinel) {
        nodes.push(x);
        x = map_ref.node_ref(x, Node::left);
    }
    nodes
}

/// An iterator over the entries of a `IntervalMap`.
#[derive(Debug)]
pub struct Iter<'a, T, V, Ix>
where
    T: Ord,
{
    /// Reference to the map
    pub(crate) map_ref: &'a IntervalMap<T, V, Ix>,
    /// Stack for iteration
    pub(crate) stack: Vec<NodeIndex<Ix>>,
}

impl<'a, T, V, Ix> Iter<'a, T, V, Ix>
where
    T: Ord,
    Ix: IndexType,
{
    pub fn new(map_ref: &'a IntervalMap<T, V, Ix>) -> Self {
        Iter {
            map_ref,
            stack: left_link(map_ref, map_ref.root),
        }
    }
}

impl<'a, T, V, Ix> Iterator for Iter<'a, T, V, Ix>
where
    T: Ord,
    Ix: IndexType,
{
    type Item = (&'a Interval<T>, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.stack.is_empty() {
            return None;
        }
        let x = self.stack.pop().unwrap();
        self.stack.extend(left_link(
            self.map_ref,
            self.map_ref.node_ref(x, Node::right),
        ));
        Some(self.map_ref.node_ref(x, |xn| (xn.interval(), xn.value())))
    }
}

/// An into iterator over the entries of a `IntervalMap`.
#[derive(Debug)]
pub struct IntoIter<T, V, Ix>
where
    T: Ord,
{
    interval_map: IntervalMap<T, V, Ix>,
    /// Stack for iteration
    pub(crate) stack: Vec<NodeIndex<Ix>>,
}

impl<T, V, Ix> IntoIter<T, V, Ix>
where
    T: Ord,
    Ix: IndexType,
{
    pub fn new(interval_map: IntervalMap<T, V, Ix>) -> Self {
        let mut temp = IntoIter {
            interval_map,
            stack: vec![],
        };
        temp.stack = left_link(&temp.interval_map, temp.interval_map.root);
        temp
    }
}

impl<T, V, Ix> Iterator for IntoIter<T, V, Ix>
where
    T: Ord,
    Ix: IndexType,
{
    type Item = (Interval<T>, V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.stack.is_empty() {
            return None;
        }
        let x = self.stack.pop().unwrap();
        self.stack.extend(left_link(
            &self.interval_map,
            self.interval_map.node_ref(x, Node::right),
        ));
        let res = &mut self.interval_map.nodes[x.index()];
        Some((res.interval.take().unwrap(), res.value.take().unwrap()))
    }
}

/// An unsorted iterator over the entries of a `IntervalMap`.
#[derive(Debug)]
pub struct UnsortedIter<'a, T, V, Ix>
where
    T: Ord,
{
    map_ref: &'a IntervalMap<T, V, Ix>,
    /// Stack for iteration
    pub(crate) cur: NodeIndex<Ix>,
}

impl<'a, T, V, Ix> UnsortedIter<'a, T, V, Ix>
where
    T: Ord,
    Ix: IndexType,
{
    pub fn new(map_ref: &'a IntervalMap<T, V, Ix>) -> Self {
        UnsortedIter {
            map_ref,
            cur: NodeIndex::SENTINEL,
        }
    }
}

impl<'a, T, V, Ix> Iterator for UnsortedIter<'a, T, V, Ix>
where
    T: Ord,
    Ix: IndexType,
{
    type Item = (&'a Interval<T>, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.map_ref.is_empty()
            || self.cur.index() >= self.map_ref.len()
            || self.cur.index() == <Ix as IndexType>::max().index()
        {
            return None;
        }
        self.cur = self.cur.incre();
        Some(
            self.map_ref
                .node_ref(self.cur, |xn| (xn.interval(), xn.value())),
        )
    }
}

/// A filter iterator over the entries of a `IntervalMap`.It's equal to `iter().filter()`
/// but faster than the latter.
#[derive(Debug)]
pub struct FilterIter<'a, T, V, Ix>
where
    T: Ord,
{
    /// Reference to the map
    pub(crate) map_ref: &'a IntervalMap<T, V, Ix>,
    /// Stack for iteration
    pub(crate) stack: Vec<NodeIndex<Ix>>,
    /// Filter criteria
    pub(crate) query: &'a Interval<T>,
}

fn left_link_with_query<T, V, Ix>(
    map_ref: &IntervalMap<T, V, Ix>,
    mut x: NodeIndex<Ix>,
    query: &Interval<T>,
) -> Vec<NodeIndex<Ix>>
where
    T: Ord,
    Ix: IndexType,
{
    let mut stack: Vec<NodeIndex<Ix>> = vec![];
    if map_ref.max(x).is_some_and(|v| v <= &query.low) {
        return stack;
    }
    while map_ref.node_ref(x, Node::sentinel).is_some() {
        if map_ref.node_ref(x, Node::interval).low < query.high {
            stack.push(x);
        }
        if map_ref.max(map_ref.node_ref(x, Node::left)) <= Some(&query.low) {
            break;
        }
        x = map_ref.node_ref(x, Node::left);
    }
    stack
}

impl<'a, T, V, Ix> FilterIter<'a, T, V, Ix>
where
    T: Ord,
    Ix: IndexType,
{
    pub fn new(map_ref: &'a IntervalMap<T, V, Ix>, query: &'a Interval<T>) -> Self {
        FilterIter {
            map_ref,
            stack: left_link_with_query(map_ref, map_ref.root, query),
            query,
        }
    }
}

impl<'a, T, V, Ix> Iterator for FilterIter<'a, T, V, Ix>
where
    T: Ord,
    Ix: IndexType,
{
    type Item = (&'a Interval<T>, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.stack.is_empty() {
            return None;
        }
        let mut x = self.stack.pop().unwrap();
        while !self.map_ref.node_ref(x, Node::interval).overlap(self.query) {
            self.stack.extend(left_link_with_query(
                self.map_ref,
                self.map_ref.node_ref(x, Node::right),
                self.query,
            ));
            if self.stack.is_empty() {
                return None;
            }
            x = self.stack.pop().unwrap();
        }
        self.stack.extend(left_link_with_query(
            self.map_ref,
            self.map_ref.node_ref(x, Node::right),
            self.query,
        ));
        Some(self.map_ref.node_ref(x, |xn| (xn.interval(), xn.value())))
    }
}
