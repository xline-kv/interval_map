//! `interval_map` is a thread-safe map based on interval tree.
//!
//! It fully implements the insertion and deletion functionality of a red-black tree,
//! ensuring that each modification operation requires at most O(logN) time complexity.
//!
//! To safely and efficiently handle insertion and deletion operations in Rust,
//! `interval_map` innovatively uses arrays to simulate pointers for managing the parent-child
//! references in the red-black tree. This approach also ensures that interval_map has the
//! `Send` and `Unpin` traits, allowing it to be safely transferred between threads and
//! to maintain a fixed memory location during asynchronous operations.
//!
//! # Example
//!
//! ```rust
//! use interval_map::{Interval, IntervalMap};
//!
//! let mut map = IntervalMap::new();
//! let int = Interval::new(1, 2);
//! map.insert(int.clone(), 123456);
//! assert_eq!(map.get(&int), Some(&123456));
//! ```
//!

mod entry;
mod index;
mod interval;
mod intervalmap;
mod iter;
mod node;

#[cfg(test)]
mod tests;

pub use entry::{Entry, OccupiedEntry, VacantEntry};
pub use interval::Interval;
pub use intervalmap::IntervalMap;
pub use iter::Iter;
