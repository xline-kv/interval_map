use crate::index::{IndexType, NodeIndex};
use crate::interval::Interval;

#[cfg(feature = "graphviz")]
use std::fmt::Display;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
/// Node of the interval tree
#[derive(Debug)]
pub struct Node<T, V, Ix>
where
    T: Ord,
{
    /// Left children
    pub left: Option<NodeIndex<Ix>>,
    /// Right children
    pub right: Option<NodeIndex<Ix>>,
    /// Parent
    pub parent: Option<NodeIndex<Ix>>,
    /// Color of the node
    pub color: Color,

    /// Interval of the node
    pub interval: Option<Interval<T>>,
    /// The index that point to the node with the max value
    pub max_index: Option<NodeIndex<Ix>>,
    /// Value of the node
    pub value: Option<V>,
}

impl<T, V, Ix> Node<T, V, Ix>
where
    T: Ord,
{
    pub fn interval(&self) -> &Interval<T> {
        self.interval.as_ref().unwrap()
    }

    pub fn value(&self) -> &V {
        self.value.as_ref().unwrap()
    }
    pub fn value_mut(&mut self) -> &mut V {
        self.value.as_mut().unwrap()
    }
    pub fn take_value(&mut self) -> V {
        self.value.take().unwrap()
    }

    pub fn set_value(value: V) -> impl FnOnce(&mut Node<T, V, Ix>) -> V {
        move |node: &mut Node<T, V, Ix>| node.value.replace(value).unwrap()
    }
}

// Convenient getter/setter methods
impl<T, V, Ix> Node<T, V, Ix>
where
    T: Ord,
    Ix: IndexType,
{
    pub(crate) fn max_index(&self) -> NodeIndex<Ix> {
        self.max_index.unwrap()
    }

    pub(crate) fn set_max_index(max_index: NodeIndex<Ix>) -> impl FnOnce(&mut Node<T, V, Ix>) {
        move |node: &mut Node<T, V, Ix>| {
            let _ignore = node.max_index.replace(max_index);
        }
    }

    pub(crate) fn left(&self) -> NodeIndex<Ix> {
        self.left.unwrap()
    }

    pub(crate) fn set_left(left: NodeIndex<Ix>) -> impl FnOnce(&mut Node<T, V, Ix>) {
        move |node: &mut Node<T, V, Ix>| {
            let _ignore = node.left.replace(left);
        }
    }

    pub(crate) fn right(&self) -> NodeIndex<Ix> {
        self.right.unwrap()
    }

    pub(crate) fn set_right(right: NodeIndex<Ix>) -> impl FnOnce(&mut Node<T, V, Ix>) {
        move |node: &mut Node<T, V, Ix>| {
            let _ignore = node.right.replace(right);
        }
    }

    pub(crate) fn parent(&self) -> NodeIndex<Ix> {
        self.parent.unwrap()
    }

    pub(crate) fn set_parent(parent: NodeIndex<Ix>) -> impl FnOnce(&mut Node<T, V, Ix>) {
        move |node: &mut Node<T, V, Ix>| {
            let _ignore = node.parent.replace(parent);
        }
    }
    pub(crate) fn is_sentinel(&self) -> bool {
        self.interval.is_none()
    }

    pub(crate) fn sentinel(&self) -> Option<&Self> {
        self.interval.is_some().then_some(self)
    }

    pub(crate) fn color(&self) -> Color {
        self.color
    }

    pub(crate) fn is_black(&self) -> bool {
        matches!(self.color, Color::Black)
    }

    pub(crate) fn is_red(&self) -> bool {
        matches!(self.color, Color::Red)
    }

    pub(crate) fn set_color(color: Color) -> impl FnOnce(&mut Node<T, V, Ix>) {
        move |node: &mut Node<T, V, Ix>| {
            node.color = color;
        }
    }
}

#[cfg(feature = "graphviz")]
impl<T, V, Ix> Node<T, V, Ix>
where
    T: Ord + Display,
    V: Display,
    Ix: IndexType,
{
    pub(crate) fn draw<W: std::io::Write>(
        &self,
        index: usize,
        mut writer: W,
    ) -> std::io::Result<()> {
        writeln!(
            writer,
            "    {} [label=\"i={}\\n{}: {}\\n\", fillcolor={}, style=filled]",
            index,
            index,
            self.interval.as_ref().unwrap(),
            self.value.as_ref().unwrap(),
            if self.is_red() { "salmon" } else { "grey65" }
        )?;
        if !self.left.unwrap().is_sentinel() {
            writeln!(
                writer,
                "    {} -> {} [label=\"L\"]",
                index,
                self.left.unwrap().index()
            )?;
        }
        if !self.right.unwrap().is_sentinel() {
            writeln!(
                writer,
                "    {} -> {} [label=\"R\"]",
                index,
                self.right.unwrap().index()
            )?;
        }
        Ok(())
    }
}

#[cfg(feature = "graphviz")]
impl<T, V, Ix> Node<T, V, Ix>
where
    T: Display + Ord,
    Ix: IndexType,
{
    pub(crate) fn draw_without_value<W: std::io::Write>(
        &self,
        index: usize,
        mut writer: W,
    ) -> std::io::Result<()> {
        writeln!(
            writer,
            "    {} [label=\"i={}: {}\", fillcolor={}, style=filled]",
            index,
            index,
            self.interval.as_ref().unwrap(),
            if self.is_red() { "salmon" } else { "grey65" }
        )?;
        if !self.left.unwrap().is_sentinel() {
            writeln!(
                writer,
                "    {} -> {} [label=\"L\"]",
                index,
                self.left.unwrap().index()
            )?;
        }
        if !self.right.unwrap().is_sentinel() {
            writeln!(
                writer,
                "    {} -> {} [label=\"R\"]",
                index,
                self.right.unwrap().index()
            )?;
        }
        Ok(())
    }
}

impl<T, V, Ix> Node<T, V, Ix>
where
    T: Ord,
    Ix: IndexType,
{
    pub fn new(interval: Interval<T>, value: V, index: NodeIndex<Ix>) -> Self {
        Node {
            interval: Some(interval),
            value: Some(value),
            max_index: Some(index),
            left: Some(NodeIndex::SENTINEL),
            right: Some(NodeIndex::SENTINEL),
            parent: Some(NodeIndex::SENTINEL),
            color: Color::Red,
        }
    }

    pub fn new_sentinel() -> Self {
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
}

/// The color of the node
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Color {
    /// Red node
    Red,
    /// Black node
    Black,
}

#[cfg(feature = "serde")]
#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{json, Value};

    #[test]
    fn test_node_serialize_deserialize() {
        let node = Node::<i32, i32, u8> {
            left: Some(NodeIndex::new(0)),
            right: Some(NodeIndex::new(1)),
            parent: Some(NodeIndex::new(2)),
            color: Color::Red,
            interval: Some(Interval::new(10, 20)),
            max_index: Some(NodeIndex::new(3)),
            value: Some(42),
        };

        // Serialize the node to JSON
        let serialized = serde_json::to_string(&node).unwrap();
        let expected = json!({
            "left": 0,
            "right": 1,
            "parent": 2,
            "color": "Red",
            "interval": [10,20],
            "max_index": 3,
            "value": 42
        });
        let actual: Value = serde_json::from_str(&serialized).unwrap();
        assert_eq!(expected, actual);

        // Deserialize the node from JSON
        let deserialized: Node<i32, i32, u8> = serde_json::from_str(&serialized).unwrap();
        assert_eq!(node.left, deserialized.left);
        assert_eq!(node.right, deserialized.right);
        assert_eq!(node.parent, deserialized.parent);
        assert_eq!(node.color, deserialized.color);
        assert_eq!(node.interval, deserialized.interval);
        assert_eq!(node.max_index, deserialized.max_index);
        assert_eq!(node.value, deserialized.value);
    }
}
