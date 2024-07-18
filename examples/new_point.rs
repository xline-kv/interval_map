use interval_map::{Interval, IntervalMap};

trait Point<T> {
    fn new_point(x: T) -> Interval<T>;
}

impl Point<u32> for Interval<u32> {
    fn new_point(x: u32) -> Self {
        Interval::new(x, x + 1)
    }
}

fn main() {
    let mut interval_map = IntervalMap::<u32, i32>::new();
    interval_map.insert(Interval::new(3, 7), 20);
    interval_map.insert(Interval::new(2, 6), 15);

    let tmp_point = Interval::new_point(5);
    assert_eq!(tmp_point, Interval::new(5, 6));

    interval_map.insert(tmp_point.clone(), 10);
    assert_eq!(interval_map.get(&tmp_point).unwrap(), &10);
    assert_eq!(
        interval_map.find_all_overlap(&Interval::new_point(5)).len(),
        3
    );
}
