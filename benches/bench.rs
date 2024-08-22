use criterion::{criterion_group, criterion_main, Bencher, Criterion};
use rand::{rngs::StdRng, Rng, SeedableRng};
use rb_interval_map::{Interval, IntervalMap};
use std::hint::black_box;

struct IntervalGenerator {
    rng: StdRng,
    limit: u32,
}
impl IntervalGenerator {
    fn new() -> Self {
        const LIMIT: u32 = 1000;
        Self {
            rng: StdRng::from_seed([0; 32]),
            limit: LIMIT,
        }
    }

    fn next(&mut self) -> Interval<u32> {
        let low = self.rng.gen_range(0..=self.limit - 1);
        let high = self.rng.gen_range(low + 1..=self.limit);
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
            black_box(map.iter().filter(|v| v.0.overlaps(&i)).collect::<Vec<_>>());
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
