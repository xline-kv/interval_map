use std::cmp;

use interval_map::{Interval, IntervalMap};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StringAffine {
    /// String
    String(String),
    /// Unbounded
    Unbounded,
}

impl StringAffine {
    pub fn new_key(s: &str) -> Self {
        Self::String(s.to_string())
    }

    pub fn new_unbounded() -> Self {
        Self::Unbounded
    }
}

impl PartialOrd for StringAffine {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for StringAffine {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        match (self, other) {
            (StringAffine::String(x), StringAffine::String(y)) => x.cmp(y),
            (StringAffine::String(_), StringAffine::Unbounded) => cmp::Ordering::Less,
            (StringAffine::Unbounded, StringAffine::String(_)) => cmp::Ordering::Greater,
            (StringAffine::Unbounded, StringAffine::Unbounded) => cmp::Ordering::Equal,
        }
    }
}

trait Point<T> {
    fn new_point(x: T) -> Interval<T>;
}

impl Point<StringAffine> for Interval<StringAffine> {
    fn new_point(x: StringAffine) -> Interval<StringAffine> {
        match x {
            StringAffine::String(mut x_string) => {
                let low = x_string.clone();
                x_string.push('\0');
                Interval::new(
                    StringAffine::new_key(&low),
                    StringAffine::new_key(&x_string),
                )
            }
            _ => panic!("new_point only receive StringAffine::String!"),
        }
    }
}

fn main() {
    let mut interval_map = IntervalMap::<StringAffine, u32>::new();
    interval_map.insert(
        Interval::new(StringAffine::new_key("8"), StringAffine::Unbounded),
        123,
    );
    assert!(interval_map.overlaps(&Interval::new_point(StringAffine::new_key("9"))));
    assert!(!interval_map.overlaps(&Interval::new_point(StringAffine::new_key("7"))));
}
