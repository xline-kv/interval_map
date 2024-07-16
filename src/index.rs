use std::fmt;
use std::hash::Hash;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

pub type DefaultIx = u32;

pub trait IndexType: Copy + Default + Hash + Ord + fmt::Debug + 'static {
    const SENTINEL: Self;
    fn new(x: usize) -> Self;
    fn index(&self) -> usize;
    fn max() -> Self;
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
                $type::MAX
            }
        }
    };
}

impl_index!(u8);
impl_index!(u16);
impl_index!(u32);
impl_index!(u64);

/// Node identifier.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Copy, Clone, Default, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct NodeIndex<Ix = DefaultIx>(Ix);

impl<Ix: IndexType> NodeIndex<Ix> {
    #[inline]
    pub fn new(x: usize) -> Self {
        NodeIndex(IndexType::new(x))
    }

    #[inline]
    pub fn end() -> Self {
        NodeIndex(IndexType::max())
    }

    pub fn incre(&self) -> Self {
        NodeIndex::new(self.index().wrapping_add(1))
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
        NodeIndex(<Ix as IndexType>::max())
    }
}

impl<Ix: fmt::Debug> fmt::Debug for NodeIndex<Ix> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "NodeIndex({:?})", self.0)
    }
}
