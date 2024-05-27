use crate::entry::{Entry, OccupiedEntry, VacantEntry};
use crate::index::{DefaultIx, IndexType, NodeIndex};
use crate::interval::{Interval, IntervalRef};
use crate::node::{Color, Node};
use std::collections::VecDeque;

/// An interval-value map, which support operations on dynamic sets of intervals.
#[derive(Debug)]
pub struct IntervalMap<T, V, Ix = DefaultIx> {
    /// Vector that stores nodes
    pub(crate) nodes: Vec<Node<T, V, Ix>>,
    /// Root of the interval tree
    pub(crate) root: NodeIndex<Ix>,
    /// Number of elements in the map
    pub(crate) len: usize,
}

impl<T, V, Ix> IntervalMap<T, V, Ix>
where
    T: Ord,
    Ix: IndexType,
{
    /// Creates a new `IntervalMap` with estimated capacity.
    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        let mut nodes = vec![Self::new_sentinel()];
        nodes.reserve(capacity);
        IntervalMap {
            nodes,
            root: Self::sentinel(),
            len: 0,
        }
    }

    /// Insert an interval-value pair into the map.
    /// If the interval exists, overwrite and return the previous value.
    ///
    /// # Panics
    ///
    /// This method panics when the tree is at the maximum number of nodes for its index
    ///
    /// # Example
    /// ```rust
    /// use interval_map::{Interval, IntervalMap};
    ///
    /// let mut map = IntervalMap::new();
    /// assert_eq!(map.insert(Interval::new(1, 3), 1), None);
    /// assert_eq!(map.insert(Interval::new(1, 3), 2), Some(1));
    /// assert_eq!(map.insert(Interval::new(1, 3), 3), Some(2));
    /// ```
    #[inline]
    pub fn insert(&mut self, interval: Interval<T>, value: V) -> Option<V> {
        let node_idx = NodeIndex::new(self.nodes.len());
        let node = Self::new_node(interval, value, node_idx);
        // check for max capacity, except if we use usize
        assert!(
            <Ix as IndexType>::max().index() == !0 || NodeIndex::end() != node_idx,
            "Reached maximum number of nodes"
        );
        self.nodes.push(node);
        self.insert_inner(node_idx)
    }

    /// Remove an interval from the map, returning the value at the interval if the interval exists
    ///
    /// # Example
    /// ```rust
    /// use interval_map::{Interval, IntervalMap};
    ///
    /// let mut map = IntervalMap::new();
    /// map.insert(Interval::new(1, 3), 1);
    /// map.insert(Interval::new(2, 4), 2);
    /// assert_eq!(map.len(), 2);
    /// assert_eq!(map.remove(&Interval::new(3, 6)), None);
    /// assert_eq!(map.len(), 2);
    /// assert_eq!(map.remove(&Interval::new(2, 4)), Some(2));
    /// assert_eq!(map.len(), 1);
    /// ```
    #[inline]
    pub fn remove(&mut self, interval: &Interval<T>) -> Option<V> {
        if let Some(node_idx) = self.search_exact(interval) {
            self.remove_inner(node_idx);
            // Swap the node with the last node stored in the vector and update indices
            let mut node = self.nodes.swap_remove(node_idx.index());
            let old = NodeIndex::<Ix>::new(self.nodes.len());
            self.update_idx(old, node_idx);

            return node.value.take();
        }
        None
    }

    /// Check if an interval in the map overlaps with the given interval.
    ///
    /// # Example
    /// ```rust
    /// use interval_map::{Interval, IntervalMap};
    ///
    /// let mut map = IntervalMap::new();
    /// map.insert(Interval::new(1, 3), ());
    /// map.insert(Interval::new(6, 7), ());
    /// map.insert(Interval::new(9, 11), ());
    /// assert!(map.overlap(&Interval::new(2, 5)));
    /// assert!(map.overlap(&Interval::new(1, 17)));
    /// assert!(!map.overlap(&Interval::new(3, 6)));
    /// assert!(!map.overlap(&Interval::new(11, 23)));
    /// ```
    #[inline]
    pub fn overlap(&self, interval: &Interval<T>) -> bool {
        let node_idx = self.search(interval);
        !self.node_ref(node_idx, Node::is_sentinel)
    }

    /// Find all intervals in the map that overlaps with the given interval.
    ///
    /// # Example
    /// ```rust
    /// use interval_map::{Interval, IntervalMap};
    ///
    /// let mut map = IntervalMap::new();
    /// map.insert(Interval::new(1, 3), ());
    /// map.insert(Interval::new(2, 4), ());
    /// map.insert(Interval::new(6, 7), ());
    /// map.insert(Interval::new(7, 11), ());
    /// assert_eq!(map.find_all_overlap(&Interval::new(2, 7)).len(), 3);
    /// map.remove(&Interval::new(1, 3));
    /// assert_eq!(map.find_all_overlap(&Interval::new(2, 7)).len(), 2);
    /// ```
    #[inline]
    pub fn find_all_overlap(&self, interval: &Interval<T>) -> Vec<(&Interval<T>, &V)> {
        if self.node_ref(self.root, Node::is_sentinel) {
            Vec::new()
        } else {
            self.find_all_overlap_inner_unordered(self.root, interval)
        }
    }

    /// Return reference to the value corresponding to the key.
    ///
    /// # Example
    /// ```rust
    /// use interval_map::{Interval, IntervalMap};
    ///
    /// let mut map = IntervalMap::new();
    /// map.insert(Interval::new(1, 3), 1);
    /// map.insert(Interval::new(7, 11), 4);
    /// assert_eq!(map.get(&Interval::new(1, 3)), Some(&1));
    /// assert_eq!(map.get(&Interval::new(7, 11)), Some(&4));
    /// assert_eq!(map.get(&Interval::new(5, 17)), None);
    /// ```
    #[inline]
    pub fn get(&self, interval: &Interval<T>) -> Option<&V> {
        self.search_exact(interval)
            .map(|idx| self.node_ref(idx, Node::value))
    }

    /// Return a reference to the value corresponding to the key.
    ///
    /// # Example
    /// ```rust
    /// use interval_map::{Interval, IntervalMap};
    ///
    /// let mut map = IntervalMap::new();
    /// map.insert(Interval::new(3, 5), 0);
    /// map.get_mut(&Interval::new(3, 5)).map(|v| *v += 1);
    /// assert_eq!(map.get(&Interval::new(3, 5)), Some(&1));
    /// ```
    #[inline]
    pub fn get_mut(&mut self, interval: &Interval<T>) -> Option<&mut V> {
        self.search_exact(interval)
            .map(|idx| self.node_mut(idx, Node::value_mut))
    }

    /// Get an iterator over the entries of the map, sorted by key.
    #[inline]
    #[must_use]
    pub fn iter(&self) -> Iter<'_, T, V, Ix> {
        Iter {
            map_ref: self,
            stack: None,
        }
    }

    /// Get the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// # Example
    /// ```rust
    /// use interval_map::{Interval, IntervalMap, Entry};
    ///
    /// let mut map = IntervalMap::new();
    ///
    /// assert!(matches!(map.entry(Interval::new(1, 2)), Entry::Vacant(_)));
    /// map.entry(Interval::new(1, 2)).or_insert(0);
    /// assert!(matches!(map.entry(Interval::new(1, 2)), Entry::Occupied(_)));
    /// map.entry(Interval::new(1, 2)).and_modify(|v| *v += 1);
    /// assert_eq!(map.get(&Interval::new(1, 2)), Some(&1));
    /// ```
    #[inline]
    pub fn entry(&mut self, interval: Interval<T>) -> Entry<'_, T, V, Ix> {
        match self.search_exact(&interval) {
            Some(node) => Entry::Occupied(OccupiedEntry {
                map_ref: self,
                node,
            }),
            None => Entry::Vacant(VacantEntry {
                map_ref: self,
                interval,
            }),
        }
    }

    /// Remove all elements from the map
    #[inline]
    pub fn clear(&mut self) {
        self.nodes.clear();
        self.nodes.push(Self::new_sentinel());
        self.root = Self::sentinel();
        self.len = 0;
    }

    /// Return the number of elements in the map.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Return `true` if the map contains no elements.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T, V> IntervalMap<T, V>
where
    T: Ord,
{
    /// Create an empty `IntervalMap`
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self {
            nodes: vec![Self::new_sentinel()],
            root: Self::sentinel(),
            len: 0,
        }
    }
}

impl<T, V> Default for IntervalMap<T, V>
where
    T: Ord,
{
    #[inline]
    fn default() -> Self {
        Self::with_capacity(0)
    }
}

impl<T, V, Ix> IntervalMap<T, V, Ix>
where
    T: Ord,
    Ix: IndexType,
{
    /// Create a new sentinel node
    fn new_sentinel() -> Node<T, V, Ix> {
        Node {
            interval: None,
            value: None,
            max_index: None,
            left: None,
            right: None,
            parent: None,
            color: Color::Black,
        }
    }

    /// Create a new tree node
    fn new_node(interval: Interval<T>, value: V, index: NodeIndex<Ix>) -> Node<T, V, Ix> {
        Node {
            max_index: Some(index),
            interval: Some(interval),
            value: Some(value),
            left: Some(Self::sentinel()),
            right: Some(Self::sentinel()),
            parent: Some(Self::sentinel()),
            color: Color::Red,
        }
    }

    /// Get the sentinel node index
    fn sentinel() -> NodeIndex<Ix> {
        NodeIndex::new(0)
    }
}

impl<T, V, Ix> IntervalMap<T, V, Ix>
where
    T: Ord,
    Ix: IndexType,
{
    /// Insert a node into the tree.
    fn insert_inner(&mut self, z: NodeIndex<Ix>) -> Option<V> {
        let mut y = Self::sentinel();
        let mut x = self.root;

        while !self.node_ref(x, Node::is_sentinel) {
            y = x;
            if self.node_ref(z, Node::interval) == self.node_ref(y, Node::interval) {
                let zval = self.node_mut(z, Node::take_value);
                let old_value = self.node_mut(y, Node::set_value(zval));
                return Some(old_value);
            }
            if self.node_ref(z, Node::interval) < self.node_ref(x, Node::interval) {
                x = self.node_ref(x, Node::left);
            } else {
                x = self.node_ref(x, Node::right);
            }
        }
        self.node_mut(z, Node::set_parent(y));
        if self.node_ref(y, Node::is_sentinel) {
            self.root = z;
        } else {
            if self.node_ref(z, Node::interval) < self.node_ref(y, Node::interval) {
                self.node_mut(y, Node::set_left(z));
            } else {
                self.node_mut(y, Node::set_right(z));
            }
            self.update_max_bottom_up(y);
        }
        self.node_mut(z, Node::set_color(Color::Red));

        self.insert_fixup(z);

        self.len = self.len.wrapping_add(1);
        None
    }

    /// Remove a node from the tree.
    fn remove_inner(&mut self, z: NodeIndex<Ix>) {
        let mut y = z;
        let mut y_orig_color = self.node_ref(y, Node::color);
        let x;
        if self.left_ref(z, Node::is_sentinel) {
            x = self.node_ref(z, Node::right);
            self.transplant(z, x);
            self.update_max_bottom_up(self.node_ref(z, Node::parent));
        } else if self.right_ref(z, Node::is_sentinel) {
            x = self.node_ref(z, Node::left);
            self.transplant(z, x);
            self.update_max_bottom_up(self.node_ref(z, Node::parent));
        } else {
            y = self.tree_minimum(self.node_ref(z, Node::right));
            let mut p = y;
            y_orig_color = self.node_ref(y, Node::color);
            x = self.node_ref(y, Node::right);
            if self.node_ref(y, Node::parent) == z {
                self.node_mut(x, Node::set_parent(y));
            } else {
                self.transplant(y, x);
                p = self.node_ref(y, Node::parent);
                self.node_mut(y, Node::set_right(self.node_ref(z, Node::right)));
                self.right_mut(y, Node::set_parent(y));
            }
            self.transplant(z, y);
            self.node_mut(y, Node::set_left(self.node_ref(z, Node::left)));
            self.left_mut(y, Node::set_parent(y));
            self.node_mut(y, Node::set_color(self.node_ref(z, Node::color)));

            self.update_max_bottom_up(p);
        }

        if matches!(y_orig_color, Color::Black) {
            self.remove_fixup(x);
        }

        self.len = self.len.wrapping_sub(1);
    }

    /// Find all intervals in the map that overlaps with the given interval.
    #[cfg(interval_tree_find_overlap_ordered)]
    fn find_all_overlap_inner(
        &self,
        x: NodeIndex<Ix>,
        interval: &Interval<T>,
    ) -> Vec<(&Interval<T>, &V)> {
        let mut list = vec![];
        if self.node_ref(x, Node::interval).overlap(interval) {
            list.push(self.node_ref(x, |nx| (nx.interval(), nx.value())));
        }
        if self.max(self.node_ref(x, Node::left)) >= Some(&interval.low) {
            list.extend(self.find_all_overlap_inner(self.node_ref(x, Node::left), interval));
        }
        if self
            .max(self.node_ref(x, Node::right))
            .map(|rmax| IntervalRef::new(&self.node_ref(x, Node::interval).low, rmax))
            .is_some_and(|i| i.overlap(interval))
        {
            list.extend(self.find_all_overlap_inner(self.node_ref(x, Node::right), interval));
        }
        list
    }

    /// Find all intervals in the map that overlaps with the given interval.
    ///
    /// The result is unordered because of breadth-first search to save stack size
    fn find_all_overlap_inner_unordered(
        &self,
        x: NodeIndex<Ix>,
        interval: &Interval<T>,
    ) -> Vec<(&Interval<T>, &V)> {
        let mut list = Vec::new();
        let mut queue = VecDeque::new();
        queue.push_back(x);
        while let Some(p) = queue.pop_front() {
            if self.node_ref(p, Node::interval).overlap(interval) {
                list.push(self.node_ref(p, |np| (np.interval(), np.value())));
            }
            let p_left = self.node_ref(p, Node::left);
            let p_right = self.node_ref(p, Node::right);
            if self.max(p_left) >= Some(&interval.low) {
                queue.push_back(p_left);
            }
            if self
                .max(self.node_ref(p, Node::right))
                .map(|rmax| IntervalRef::new(&self.node_ref(p, Node::interval).low, rmax))
                .is_some_and(|i| i.overlap(interval))
            {
                queue.push_back(p_right);
            }
        }

        list
    }

    /// Search for an interval that overlaps with the given interval.
    fn search(&self, interval: &Interval<T>) -> NodeIndex<Ix> {
        let mut x = self.root;
        while self
            .node_ref(x, Node::sentinel)
            .map(Node::interval)
            .is_some_and(|xi| !xi.overlap(interval))
        {
            if self.max(self.node_ref(x, Node::left)) > Some(&interval.low) {
                x = self.node_ref(x, Node::left);
            } else {
                x = self.node_ref(x, Node::right);
            }
        }
        x
    }

    /// Search for the node with exact the given interval
    fn search_exact(&self, interval: &Interval<T>) -> Option<NodeIndex<Ix>> {
        let mut x = self.root;
        while !self.node_ref(x, Node::is_sentinel) {
            if self.node_ref(x, Node::interval) == interval {
                return Some(x);
            }
            if self.max(x) < Some(&interval.high) {
                return None;
            }
            if self.node_ref(x, Node::interval) > interval {
                x = self.node_ref(x, Node::left);
            } else {
                x = self.node_ref(x, Node::right);
            }
        }
        None
    }

    /// Restore red-black tree properties after an insert.
    fn insert_fixup(&mut self, mut z: NodeIndex<Ix>) {
        while self.parent_ref(z, Node::is_red) {
            if self.grand_parent_ref(z, Node::is_sentinel) {
                break;
            }
            if self.is_left_child(self.node_ref(z, Node::parent)) {
                let y = self.grand_parent_ref(z, Node::right);
                if self.node_ref(y, Node::is_red) {
                    self.parent_mut(z, Node::set_color(Color::Black));
                    self.node_mut(y, Node::set_color(Color::Black));
                    self.grand_parent_mut(z, Node::set_color(Color::Red));
                    z = self.parent_ref(z, Node::parent);
                } else {
                    if self.is_right_child(z) {
                        z = self.node_ref(z, Node::parent);
                        self.left_rotate(z);
                    }
                    self.parent_mut(z, Node::set_color(Color::Black));
                    self.grand_parent_mut(z, Node::set_color(Color::Red));
                    self.right_rotate(self.parent_ref(z, Node::parent));
                }
            } else {
                let y = self.grand_parent_ref(z, Node::left);
                if self.node_ref(y, Node::is_red) {
                    self.parent_mut(z, Node::set_color(Color::Black));
                    self.node_mut(y, Node::set_color(Color::Black));
                    self.grand_parent_mut(z, Node::set_color(Color::Red));
                    z = self.parent_ref(z, Node::parent);
                } else {
                    if self.is_left_child(z) {
                        z = self.node_ref(z, Node::parent);
                        self.right_rotate(z);
                    }
                    self.parent_mut(z, Node::set_color(Color::Black));
                    self.grand_parent_mut(z, Node::set_color(Color::Red));
                    self.left_rotate(self.parent_ref(z, Node::parent));
                }
            }
        }
        self.node_mut(self.root, Node::set_color(Color::Black));
    }

    /// Restore red-black tree properties after a remove.
    fn remove_fixup(&mut self, mut x: NodeIndex<Ix>) {
        while x != self.root && self.node_ref(x, Node::is_black) {
            let mut w;
            if self.is_left_child(x) {
                w = self.parent_ref(x, Node::right);
                if self.node_ref(w, Node::is_red) {
                    self.node_mut(w, Node::set_color(Color::Black));
                    self.parent_mut(x, Node::set_color(Color::Red));
                    self.left_rotate(self.node_ref(x, Node::parent));
                    w = self.parent_ref(x, Node::right);
                }
                if self.node_ref(w, Node::is_sentinel) {
                    break;
                }
                if self.left_ref(w, Node::is_black) && self.right_ref(w, Node::is_black) {
                    self.node_mut(w, Node::set_color(Color::Red));
                    x = self.node_ref(x, Node::parent);
                } else {
                    if self.right_ref(w, Node::is_black) {
                        self.left_mut(w, Node::set_color(Color::Black));
                        self.node_mut(w, Node::set_color(Color::Red));
                        self.right_rotate(w);
                        w = self.parent_ref(x, Node::right);
                    }
                    self.node_mut(w, Node::set_color(self.parent_ref(x, Node::color)));
                    self.parent_mut(x, Node::set_color(Color::Black));
                    self.right_mut(w, Node::set_color(Color::Black));
                    self.left_rotate(self.node_ref(x, Node::parent));
                    x = self.root;
                }
            } else {
                w = self.parent_ref(x, Node::left);
                if self.node_ref(w, Node::is_red) {
                    self.node_mut(w, Node::set_color(Color::Black));
                    self.parent_mut(x, Node::set_color(Color::Red));
                    self.right_rotate(self.node_ref(x, Node::parent));
                    w = self.parent_ref(x, Node::left);
                }
                if self.node_ref(w, Node::is_sentinel) {
                    break;
                }
                if self.right_ref(w, Node::is_black) && self.left_ref(w, Node::is_black) {
                    self.node_mut(w, Node::set_color(Color::Red));
                    x = self.node_ref(x, Node::parent);
                } else {
                    if self.left_ref(w, Node::is_black) {
                        self.right_mut(w, Node::set_color(Color::Black));
                        self.node_mut(w, Node::set_color(Color::Red));
                        self.left_rotate(w);
                        w = self.parent_ref(x, Node::left);
                    }
                    self.node_mut(w, Node::set_color(self.parent_ref(x, Node::color)));
                    self.parent_mut(x, Node::set_color(Color::Black));
                    self.left_mut(w, Node::set_color(Color::Black));
                    self.right_rotate(self.node_ref(x, Node::parent));
                    x = self.root;
                }
            }
        }
        self.node_mut(x, Node::set_color(Color::Black));
    }

    /// Binary tree left rotate.
    fn left_rotate(&mut self, x: NodeIndex<Ix>) {
        if self.right_ref(x, Node::is_sentinel) {
            return;
        }
        let y = self.node_ref(x, Node::right);
        self.node_mut(x, Node::set_right(self.node_ref(y, Node::left)));
        if !self.left_ref(y, Node::is_sentinel) {
            self.left_mut(y, Node::set_parent(x));
        }

        self.replace_parent(x, y);
        self.node_mut(y, Node::set_left(x));

        self.rotate_update_max(x, y);
    }

    /// Binary tree right rotate.
    fn right_rotate(&mut self, x: NodeIndex<Ix>) {
        if self.left_ref(x, Node::is_sentinel) {
            return;
        }
        let y = self.node_ref(x, Node::left);
        self.node_mut(x, Node::set_left(self.node_ref(y, Node::right)));
        if !self.right_ref(y, Node::is_sentinel) {
            self.right_mut(y, Node::set_parent(x));
        }

        self.replace_parent(x, y);
        self.node_mut(y, Node::set_right(x));

        self.rotate_update_max(x, y);
    }

    /// Replace parent during a rotation.
    fn replace_parent(&mut self, x: NodeIndex<Ix>, y: NodeIndex<Ix>) {
        self.node_mut(y, Node::set_parent(self.node_ref(x, Node::parent)));
        if self.parent_ref(x, Node::is_sentinel) {
            self.root = y;
        } else if self.is_left_child(x) {
            self.parent_mut(x, Node::set_left(y));
        } else {
            self.parent_mut(x, Node::set_right(y));
        }
        self.node_mut(x, Node::set_parent(y));
    }

    /// Update the max value after a rotation.
    fn rotate_update_max(&mut self, x: NodeIndex<Ix>, y: NodeIndex<Ix>) {
        self.node_mut(y, Node::set_max_index(self.node_ref(x, Node::max_index)));
        self.recaculate_max(x);
    }

    /// Update the max value towards the root
    fn update_max_bottom_up(&mut self, x: NodeIndex<Ix>) {
        let mut p = x;
        while !self.node_ref(p, Node::is_sentinel) {
            self.recaculate_max(p);
            p = self.node_ref(p, Node::parent);
        }
    }

    /// Recaculate max value from left and right childrens
    fn recaculate_max(&mut self, x: NodeIndex<Ix>) {
        self.node_mut(x, Node::set_max_index(x));
        let x_left = self.node_ref(x, Node::left);
        let x_right = self.node_ref(x, Node::right);
        if self.max(x_left) > self.max(x) {
            self.node_mut(
                x,
                Node::set_max_index(self.node_ref(x_left, Node::max_index)),
            );
        }
        if self.max(x_right) > self.max(x) {
            self.node_mut(
                x,
                Node::set_max_index(self.node_ref(x_right, Node::max_index)),
            );
        }
    }

    /// Find the node with the minimum interval.
    fn tree_minimum(&self, mut x: NodeIndex<Ix>) -> NodeIndex<Ix> {
        while !self.left_ref(x, Node::is_sentinel) {
            x = self.node_ref(x, Node::left);
        }
        x
    }

    /// Replace one subtree as a child of its parent with another subtree.
    fn transplant(&mut self, u: NodeIndex<Ix>, v: NodeIndex<Ix>) {
        if self.parent_ref(u, Node::is_sentinel) {
            self.root = v;
        } else if self.is_left_child(u) {
            self.parent_mut(u, Node::set_left(v));
        } else {
            self.parent_mut(u, Node::set_right(v));
        }
        self.node_mut(v, Node::set_parent(self.node_ref(u, Node::parent)));
    }

    /// Check if a node is a left child of its parent.
    fn is_left_child(&self, node: NodeIndex<Ix>) -> bool {
        self.parent_ref(node, Node::left) == node
    }

    /// Check if a node is a right child of its parent.
    fn is_right_child(&self, node: NodeIndex<Ix>) -> bool {
        self.parent_ref(node, Node::right) == node
    }

    /// Update nodes indices after remove
    ///
    /// This method has a time complexity of `O(logn)`, as we need to
    /// update the max index from bottom to top.
    fn update_idx(&mut self, old: NodeIndex<Ix>, new: NodeIndex<Ix>) {
        if self.root == old {
            self.root = new;
        }
        if self.nodes.get(new.index()).is_some() {
            if !self.parent_ref(new, Node::is_sentinel) {
                if self.parent_ref(new, Node::left) == old {
                    self.parent_mut(new, Node::set_left(new));
                } else {
                    self.parent_mut(new, Node::set_right(new));
                }
            }
            self.left_mut(new, Node::set_parent(new));
            self.right_mut(new, Node::set_parent(new));

            let mut p = new;
            while !self.node_ref(p, Node::is_sentinel) {
                if self.node_ref(p, Node::max_index) == old {
                    self.node_mut(p, Node::set_max_index(new));
                }
                p = self.node_ref(p, Node::parent);
            }
        }
    }
}

// Convenient methods for reference or mutate current/parent/left/right node
impl<'a, T, V, Ix> IntervalMap<T, V, Ix>
where
    Ix: IndexType,
{
    fn node_ref<F, R>(&'a self, node: NodeIndex<Ix>, op: F) -> R
    where
        R: 'a,
        F: FnOnce(&'a Node<T, V, Ix>) -> R,
    {
        op(&self.nodes[node.index()])
    }

    pub(crate) fn node_mut<F, R>(&'a mut self, node: NodeIndex<Ix>, op: F) -> R
    where
        R: 'a,
        F: FnOnce(&'a mut Node<T, V, Ix>) -> R,
    {
        op(&mut self.nodes[node.index()])
    }

    fn left_ref<F, R>(&'a self, node: NodeIndex<Ix>, op: F) -> R
    where
        R: 'a,
        F: FnOnce(&'a Node<T, V, Ix>) -> R,
    {
        let idx = self.nodes[node.index()].left().index();
        op(&self.nodes[idx])
    }

    fn right_ref<F, R>(&'a self, node: NodeIndex<Ix>, op: F) -> R
    where
        R: 'a,
        F: FnOnce(&'a Node<T, V, Ix>) -> R,
    {
        let idx = self.nodes[node.index()].right().index();
        op(&self.nodes[idx])
    }

    fn parent_ref<F, R>(&'a self, node: NodeIndex<Ix>, op: F) -> R
    where
        R: 'a,
        F: FnOnce(&'a Node<T, V, Ix>) -> R,
    {
        let idx = self.nodes[node.index()].parent().index();
        op(&self.nodes[idx])
    }

    fn grand_parent_ref<F, R>(&'a self, node: NodeIndex<Ix>, op: F) -> R
    where
        R: 'a,
        F: FnOnce(&'a Node<T, V, Ix>) -> R,
    {
        let parent_idx = self.nodes[node.index()].parent().index();
        let grand_parent_idx = self.nodes[parent_idx].parent().index();
        op(&self.nodes[grand_parent_idx])
    }

    fn left_mut<F, R>(&'a mut self, node: NodeIndex<Ix>, op: F) -> R
    where
        R: 'a,
        F: FnOnce(&'a mut Node<T, V, Ix>) -> R,
    {
        let idx = self.nodes[node.index()].left().index();
        op(&mut self.nodes[idx])
    }

    fn right_mut<F, R>(&'a mut self, node: NodeIndex<Ix>, op: F) -> R
    where
        R: 'a,
        F: FnOnce(&'a mut Node<T, V, Ix>) -> R,
    {
        let idx = self.nodes[node.index()].right().index();
        op(&mut self.nodes[idx])
    }

    fn parent_mut<F, R>(&'a mut self, node: NodeIndex<Ix>, op: F) -> R
    where
        R: 'a,
        F: FnOnce(&'a mut Node<T, V, Ix>) -> R,
    {
        let idx = self.nodes[node.index()].parent().index();
        op(&mut self.nodes[idx])
    }

    fn grand_parent_mut<F, R>(&'a mut self, node: NodeIndex<Ix>, op: F) -> R
    where
        R: 'a,
        F: FnOnce(&'a mut Node<T, V, Ix>) -> R,
    {
        let parent_idx = self.nodes[node.index()].parent().index();
        let grand_parent_idx = self.nodes[parent_idx].parent().index();
        op(&mut self.nodes[grand_parent_idx])
    }

    fn max(&self, node: NodeIndex<Ix>) -> Option<&T> {
        let max_index = self.nodes[node.index()].max_index?.index();
        self.nodes[max_index].interval.as_ref().map(|i| &i.high)
    }
}

/// An iterator over the entries of a `IntervalMap`.
#[derive(Debug)]
pub struct Iter<'a, T, V, Ix> {
    /// Reference to the map
    map_ref: &'a IntervalMap<T, V, Ix>,
    /// Stack for iteration
    stack: Option<Vec<NodeIndex<Ix>>>,
}

impl<T, V, Ix> Iter<'_, T, V, Ix>
where
    Ix: IndexType,
{
    /// Initializes the stack
    fn init_stack(&mut self) {
        self.stack = Some(Self::left_link(self.map_ref, self.map_ref.root));
    }

    /// Pushes a link of nodes on the left to stack.
    fn left_link(map_ref: &IntervalMap<T, V, Ix>, mut x: NodeIndex<Ix>) -> Vec<NodeIndex<Ix>> {
        let mut nodes = vec![];
        while !map_ref.node_ref(x, Node::is_sentinel) {
            nodes.push(x);
            x = map_ref.node_ref(x, Node::left);
        }
        nodes
    }
}

impl<'a, T, V, Ix> Iterator for Iter<'a, T, V, Ix>
where
    Ix: IndexType,
{
    type Item = (&'a Interval<T>, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.stack.is_none() {
            self.init_stack();
        }
        let stack = self.stack.as_mut().unwrap();
        if stack.is_empty() {
            return None;
        }
        let x = stack.pop().unwrap();
        stack.extend(Self::left_link(
            self.map_ref,
            self.map_ref.node_ref(x, Node::right),
        ));
        Some(self.map_ref.node_ref(x, |xn| (xn.interval(), xn.value())))
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use rand::{rngs::StdRng, Rng, SeedableRng};

    use super::*;

    struct IntervalGenerator {
        rng: StdRng,
        unique: HashSet<Interval<i32>>,
        limit: i32,
    }

    impl IntervalGenerator {
        fn new(seed: [u8; 32]) -> Self {
            const LIMIT: i32 = 1000;
            Self {
                rng: SeedableRng::from_seed(seed),
                unique: HashSet::new(),
                limit: LIMIT,
            }
        }

        fn next(&mut self) -> Interval<i32> {
            let low = self.rng.gen_range(0..self.limit - 1);
            let high = self.rng.gen_range((low + 1)..self.limit);
            Interval::new(low, high)
        }

        fn next_unique(&mut self) -> Interval<i32> {
            let mut interval = self.next();
            while self.unique.contains(&interval) {
                interval = self.next();
            }
            self.unique.insert(interval.clone());
            interval
        }

        fn next_with_range(&mut self, range: i32) -> Interval<i32> {
            let low = self.rng.gen_range(0..self.limit - 1);
            let high = self
                .rng
                .gen_range((low + 1)..self.limit.min(low + 1 + range));
            Interval::new(low, high)
        }
    }

    impl<V> IntervalMap<i32, V> {
        fn check_max(&self) {
            let _ignore = self.check_max_inner(self.root);
        }

        fn check_max_inner(&self, x: NodeIndex<u32>) -> i32 {
            if self.node_ref(x, Node::is_sentinel) {
                return 0;
            }
            let l_max = self.check_max_inner(self.node_ref(x, Node::left));
            let r_max = self.check_max_inner(self.node_ref(x, Node::right));
            let max = self.node_ref(x, |x| x.interval().high.max(l_max).max(r_max));
            assert_eq!(self.max(x), Some(&max));
            max
        }

        /// 1. Every node is either red or black.
        /// 2. The root is black.
        /// 3. Every leaf (NIL) is black.
        /// 4. If a node is red, then both its children are black.
        /// 5. For each node, all simple paths from the node to descendant leaves contain the
        /// same number of black nodes.
        fn check_rb_properties(&self) {
            assert!(matches!(
                self.node_ref(self.root, Node::color),
                Color::Black
            ));
            self.check_children_color(self.root);
            self.check_black_height(self.root);
        }

        fn check_children_color(&self, x: NodeIndex<u32>) {
            if self.node_ref(x, Node::is_sentinel) {
                return;
            }
            self.check_children_color(self.node_ref(x, Node::left));
            self.check_children_color(self.node_ref(x, Node::right));
            if self.node_ref(x, Node::is_red) {
                assert!(matches!(self.left_ref(x, Node::color), Color::Black));
                assert!(matches!(self.right_ref(x, Node::color), Color::Black));
            }
        }

        fn check_black_height(&self, x: NodeIndex<u32>) -> usize {
            if self.node_ref(x, Node::is_sentinel) {
                return 0;
            }
            let lefth = self.check_black_height(self.node_ref(x, Node::left));
            let righth = self.check_black_height(self.node_ref(x, Node::right));
            assert_eq!(lefth, righth);
            if self.node_ref(x, Node::is_black) {
                return lefth + 1;
            }
            lefth
        }
    }

    fn with_map_and_generator<V>(test_fn: impl Fn(IntervalMap<i32, V>, IntervalGenerator)) {
        let seeds = vec![[0; 32], [1; 32], [2; 32]];
        for seed in seeds {
            let gen = IntervalGenerator::new(seed);
            let map = IntervalMap::new();
            test_fn(map, gen);
        }
    }

    #[test]
    fn red_black_tree_properties_is_satisfied() {
        with_map_and_generator(|mut map, mut gen| {
            let intervals: Vec<_> = std::iter::repeat_with(|| gen.next_unique())
                .take(1000)
                .collect();
            for i in intervals.clone() {
                let _ignore = map.insert(i, ());
            }
            map.check_rb_properties();
        });
    }

    #[test]
    fn map_len_will_update() {
        with_map_and_generator(|mut map, mut gen| {
            let intervals: Vec<_> = std::iter::repeat_with(|| gen.next_unique())
                .take(100)
                .collect();
            for i in intervals.clone() {
                let _ignore = map.insert(i, ());
            }
            assert_eq!(map.len(), 100);
            for i in intervals {
                let _ignore = map.remove(&i);
            }
            assert_eq!(map.len(), 0);
        });
    }

    #[test]
    fn check_overlap_is_ok() {
        with_map_and_generator(|mut map, mut gen| {
            let intervals: Vec<_> = std::iter::repeat_with(|| gen.next_with_range(10))
                .take(100)
                .collect();
            for i in intervals.clone() {
                let _ignore = map.insert(i, ());
            }
            let to_check: Vec<_> = std::iter::repeat_with(|| gen.next_with_range(10))
                .take(1000)
                .collect();
            let expects: Vec<_> = to_check
                .iter()
                .map(|ci| intervals.iter().any(|i| ci.overlap(i)))
                .collect();

            for (ci, expect) in to_check.into_iter().zip(expects.into_iter()) {
                assert_eq!(map.overlap(&ci), expect);
            }
        });
    }

    #[test]
    fn check_max_is_ok() {
        with_map_and_generator(|mut map, mut gen| {
            let intervals: Vec<_> = std::iter::repeat_with(|| gen.next_unique())
                .take(1000)
                .collect();
            for i in intervals.clone() {
                let _ignore = map.insert(i, ());
                map.check_max();
            }
            assert_eq!(map.len(), 1000);
            for i in intervals {
                let _ignore = map.remove(&i);
                map.check_max();
            }
        });
    }

    #[test]
    fn remove_non_exist_interval_will_do_nothing() {
        with_map_and_generator(|mut map, mut gen| {
            let intervals: Vec<_> = std::iter::repeat_with(|| gen.next_unique())
                .take(1000)
                .collect();
            for i in intervals {
                let _ignore = map.insert(i, ());
            }
            assert_eq!(map.len(), 1000);
            let to_remove: Vec<_> = std::iter::repeat_with(|| gen.next_unique())
                .take(1000)
                .collect();
            for i in to_remove {
                let _ignore = map.remove(&i);
            }
            assert_eq!(map.len(), 1000);
        });
    }

    #[test]
    fn find_all_overlap_is_ok() {
        with_map_and_generator(|mut map, mut gen| {
            let intervals: Vec<_> = std::iter::repeat_with(|| gen.next_unique())
                .take(1000)
                .collect();
            for i in intervals.clone() {
                let _ignore = map.insert(i, ());
            }
            let to_find: Vec<_> = std::iter::repeat_with(|| gen.next()).take(1000).collect();

            let expects: Vec<Vec<_>> = to_find
                .iter()
                .map(|ti| intervals.iter().filter(|i| ti.overlap(i)).collect())
                .collect();

            for (ti, mut expect) in to_find.into_iter().zip(expects.into_iter()) {
                let mut result = map.find_all_overlap(&ti);
                expect.sort_unstable();
                result.sort_unstable();
                assert_eq!(expect.len(), result.len());
                for (e, r) in expect.into_iter().zip(result.into_iter()) {
                    assert_eq!(e, r.0);
                }
            }
        });
    }

    #[test]
    fn iterate_through_map_is_sorted() {
        with_map_and_generator(|mut map, mut gen| {
            let mut intervals: Vec<_> = std::iter::repeat_with(|| gen.next_unique())
                .enumerate()
                .take(1000)
                .collect();
            for (v, i) in intervals.clone() {
                let _ignore = map.insert(i, v);
            }
            intervals.sort_unstable_by(|a, b| a.1.cmp(&b.1));

            for ((ei, ev), (v, i)) in map.iter().zip(intervals.iter()) {
                assert_eq!(ei, i);
                assert_eq!(ev, v);
            }
        });
    }

    #[test]
    fn interval_map_clear_is_ok() {
        let mut map = IntervalMap::new();
        map.insert(Interval::new(1, 3), 1);
        map.insert(Interval::new(2, 4), 2);
        map.insert(Interval::new(6, 7), 3);
        assert_eq!(map.len(), 3);
        map.clear();
        assert_eq!(map.len(), 0);
        assert!(map.is_empty());
        assert_eq!(map.nodes.len(), 1);
        assert!(map.nodes[0].is_sentinel());
    }
}
