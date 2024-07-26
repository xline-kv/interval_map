use std::fmt;
use std::hash::Hash;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Trait for the unsigned integer type used for node indices.
pub trait IndexType: Copy + Default + Hash + Ord + fmt::Debug + 'static {
    const SENTINEL: Self;

    /// Convert x from usize to the corresponding type
    /// # Notice
    /// Using u8 and u16 types may cause numerical overflow. Please check the numerical range before using
    fn new(x: usize) -> Self;

    /// Convert self to usize
    fn index(&self) -> usize;

    /// Return Self::MAX
    fn max() -> Self;

    /// Check if self is Self::SENTINEL
    fn is_sentinel(&self) -> bool {
        *self == Self::SENTINEL
    }
}

macro_rules! impl_index {
    ($type:ident) => {
        impl IndexType for $type {
            const SENTINEL: Self = 0;

            #[inline(always)]
            fn new(x: usize) -> Self {
                x as $type
            }
            #[inline(always)]
            fn index(&self) -> usize {
                *self as usize
            }
            #[inline(always)]
            fn max() -> Self {
                Self::MAX
            }
        }
    };
}

impl_index!(u8);
impl_index!(u16);
impl_index!(u32);
impl_index!(u64);

pub type DefaultIx = u32;

/// Node identifier.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Copy, Clone, Default, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct NodeIndex<Ix = DefaultIx>(Ix);

impl<Ix: IndexType> NodeIndex<Ix> {
    #[inline]
    pub fn new(x: usize) -> Self {
        NodeIndex(IndexType::new(x))
    }

    pub fn inc(&self) -> Self {
        if self.index() == <Ix as IndexType>::max().index() {
            panic!("Index will overflow!")
        }
        NodeIndex::new(self.index() + 1)
    }
}

impl<Ix: IndexType> IndexType for NodeIndex<Ix> {
    const SENTINEL: Self = NodeIndex(Ix::SENTINEL);

    #[inline]
    fn index(&self) -> usize {
        self.0.index()
    }

    #[inline]
    fn new(x: usize) -> Self {
        NodeIndex::new(x)
    }

    #[inline]
    fn max() -> Self {
        NodeIndex(IndexType::max())
    }
}

impl<Ix: fmt::Debug> fmt::Debug for NodeIndex<Ix> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "NodeIndex({:?})", self.0)
    }
}
