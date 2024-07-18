use criterion::{criterion_group, criterion_main, Bencher, Criterion};
use interval_map::{Interval, IntervalMap};
use rand::{rngs::StdRng, Rng, SeedableRng};
use std::hint::black_box;

struct IntervalGenerator {
    rng: StdRng,
}
impl IntervalGenerator {
    fn new() -> Self {
        let seed: [u8; 32] = [
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
            24, 25, 26, 27, 28, 29, 30, 31,
        ];
        Self {
            rng: StdRng::from_seed(seed),
        }
    }

    fn next(&mut self) -> Interval<u32> {
        let low = self.rng.gen();
        let high = self.rng.gen_range(low + 1..=u32::MAX);
        Interval::new(low, high)
    }
}

// insert helper fn
fn interval_map_insert(count: usize, bench: &mut Bencher) {
    let mut gen = IntervalGenerator::new();
    let intervals: Vec<_> = std::iter::repeat_with(|| gen.next()).take(count).collect();
    bench.iter(|| {
        let mut map = IntervalMap::new();
        for i in intervals.clone() {
            black_box(map.insert(i, ()));
        }
    });
}

// insert and remove helper fn
fn interval_map_insert_remove(count: usize, bench: &mut Bencher) {
    let mut gen = IntervalGenerator::new();
    let intervals: Vec<_> = std::iter::repeat_with(|| gen.next()).take(count).collect();
    bench.iter(|| {
        let mut map = IntervalMap::new();
        for i in intervals.clone() {
            black_box(map.insert(i, ()));
        }
        for i in &intervals {
            black_box(map.remove(i));
        }
    });
}

fn bench_interval_map_insert(c: &mut Criterion) {
    c.bench_function("bench_interval_map_insert_100", |b| {
        interval_map_insert(100, b)
    });
    c.bench_function("bench_interval_map_insert_1000", |b| {
        interval_map_insert(1000, b)
    });
    c.bench_function("bench_interval_map_insert_10,000", |b| {
        interval_map_insert(10_000, b)
    });
    c.bench_function("bench_interval_map_insert_100,000", |b| {
        interval_map_insert(100_000, b)
    });
}

fn bench_interval_map_insert_remove(c: &mut Criterion) {
    c.bench_function("bench_interval_map_insert_remove_100", |b| {
        interval_map_insert_remove(100, b)
    });
    c.bench_function("bench_interval_map_insert_remove_1000", |b| {
        interval_map_insert_remove(1000, b)
    });
    c.bench_function("bench_interval_map_insert_remove_10,000", |b| {
        interval_map_insert_remove(10_000, b)
    });
    c.bench_function("bench_interval_map_insert_remove_100,000", |b| {
        interval_map_insert_remove(100_000, b)
    });
}

// FilterIter helper fn
fn interval_map_filter_iter(count: usize, bench: &mut Bencher) {
    let mut gen = IntervalGenerator::new();
    let intervals: Vec<_> = std::iter::repeat_with(|| gen.next()).take(count).collect();
    let mut map = IntervalMap::new();
    for i in intervals.clone() {
        map.insert(i, ());
    }
    bench.iter(|| {
        for i in intervals.clone() {
            black_box(map.filter_iter(&i).collect::<Vec<_>>());
        }
    });
}

// iter().filter() helper fn
fn interval_map_iter_filter(count: usize, bench: &mut Bencher) {
    let mut gen = IntervalGenerator::new();
    let intervals: Vec<_> = std::iter::repeat_with(|| gen.next()).take(count).collect();
    let mut map = IntervalMap::new();
    for i in intervals.clone() {
        map.insert(i, ());
    }
    bench.iter(|| {
        for i in intervals.clone() {
            black_box(map.iter().filter(|v| v.0.overlap(&i)).collect::<Vec<_>>());
        }
    });
}

fn bench_interval_map_filter_iter(c: &mut Criterion) {
    c.bench_function("bench_interval_map_filter_iter_100", |b| {
        interval_map_filter_iter(100, b)
    });
    c.bench_function("bench_interval_map_filter_iter_1000", |b| {
        interval_map_filter_iter(1000, b)
    });
}

fn bench_interval_map_iter_filter(c: &mut Criterion) {
    c.bench_function("bench_interval_map_iter_filter_100", |b| {
        interval_map_iter_filter(100, b)
    });
    c.bench_function("bench_interval_map_iter_filter_1000", |b| {
        interval_map_iter_filter(1000, b)
    });
}

fn criterion_config() -> Criterion {
    Criterion::default().configure_from_args().without_plots()
}

criterion_group! {
    name = benches_basic_op;
    config = criterion_config();
    targets = bench_interval_map_insert, bench_interval_map_insert_remove,
}

criterion_group! {
    name = benches_iter;
    config = criterion_config();
    targets = bench_interval_map_filter_iter, bench_interval_map_iter_filter
}

criterion_main!(benches_basic_op, benches_iter);