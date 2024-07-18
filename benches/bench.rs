use criterion::{criterion_group, criterion_main, Bencher, Criterion};
use interval_map::{Interval, IntervalMap};
use std::hint::black_box;

struct Rng {
    state: u32,
}
impl Rng {
    fn new() -> Self {
        Self { state: 0x87654321 }
    }

    fn gen_u32(&mut self) -> u32 {
        self.state ^= self.state << 13;
        self.state ^= self.state >> 17;
        self.state ^= self.state << 5;
        self.state
    }

    fn gen_range_i32(&mut self, low: i32, high: i32) -> i32 {
        let d = (high - low) as u32;
        low + (self.gen_u32() % d) as i32
    }
}

struct IntervalGenerator {
    rng: Rng,
    limit: i32,
}
impl IntervalGenerator {
    fn new() -> Self {
        const LIMIT: i32 = 100000;
        Self {
            rng: Rng::new(),
            limit: LIMIT,
        }
    }

    fn next(&mut self) -> Interval<i32> {
        let low = self.rng.gen_range_i32(0, self.limit - 1);
        let high = self.rng.gen_range_i32(low + 1, self.limit);
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
            black_box(map.remove(&i));
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

fn criterion_config() -> Criterion {
    Criterion::default().configure_from_args().without_plots()
}

criterion_group! {
    name = benches;
    config = criterion_config();
    targets = bench_interval_map_insert, bench_interval_map_insert_remove
}

criterion_main!(benches);
