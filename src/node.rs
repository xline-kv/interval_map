use crate::interval::Interval;

use crate::index::{IndexType, NodeIndex};

/// Node of the interval tree
#[derive(Debug)]
pub struct Node<T, V, Ix> {
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

// Convenient getter/setter methods
impl<T, V, Ix> Node<T, V, Ix>
where
    Ix: IndexType,
{
    pub fn color(&self) -> Color {
        self.color
    }

    pub fn interval(&self) -> &Interval<T> {
        self.interval.as_ref().unwrap()
    }

    pub fn max_index(&self) -> NodeIndex<Ix> {
        self.max_index.unwrap()
    }

    pub fn left(&self) -> NodeIndex<Ix> {
        self.left.unwrap()
    }

    pub fn right(&self) -> NodeIndex<Ix> {
        self.right.unwrap()
    }

    pub fn parent(&self) -> NodeIndex<Ix> {
        self.parent.unwrap()
    }

    pub fn is_sentinel(&self) -> bool {
        self.interval.is_none()
    }

    pub fn sentinel(&self) -> Option<&Self> {
        self.interval.is_some().then_some(self)
    }

    pub fn is_black(&self) -> bool {
        matches!(self.color, Color::Black)
    }

    pub fn is_red(&self) -> bool {
        matches!(self.color, Color::Red)
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

    pub fn set_color(color: Color) -> impl FnOnce(&mut Node<T, V, Ix>) {
        move |node: &mut Node<T, V, Ix>| {
            node.color = color;
        }
    }

    pub fn set_max_index(max_index: NodeIndex<Ix>) -> impl FnOnce(&mut Node<T, V, Ix>) {
        move |node: &mut Node<T, V, Ix>| {
            let _ignore = node.max_index.replace(max_index);
        }
    }

    pub fn set_left(left: NodeIndex<Ix>) -> impl FnOnce(&mut Node<T, V, Ix>) {
        move |node: &mut Node<T, V, Ix>| {
            let _ignore = node.left.replace(left);
        }
    }

    pub fn set_right(right: NodeIndex<Ix>) -> impl FnOnce(&mut Node<T, V, Ix>) {
        move |node: &mut Node<T, V, Ix>| {
            let _ignore = node.right.replace(right);
        }
    }

    pub fn set_parent(parent: NodeIndex<Ix>) -> impl FnOnce(&mut Node<T, V, Ix>) {
        move |node: &mut Node<T, V, Ix>| {
            let _ignore = node.parent.replace(parent);
        }
    }
}

/// The color of the node
#[derive(Debug, Clone, Copy)]
pub enum Color {
    /// Red node
    Red,
    /// Black node
    Black,
}
