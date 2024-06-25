# interval_map

`interval_map` is a map based on interval tree. It fully implements the insertion and deletion functionality of a red-black tree, ensuring that each modification operation requires at most $O(logN)$ time complexity.

The implementation of the interval tree in interval_map references "Introduction to Algorithms" (3rd ed., Section 14.3: Interval trees, pp. 348–354).

To safely and efficiently handle insertion and deletion operations in Rust, `interval_map` innovatively **uses arrays to simulate pointers** for managing the parent-child references in the red-black tree. This approach also ensures that interval_map has the `Send` and `Unpin` traits, allowing it to be safely transferred between threads and to maintain a fixed memory location during asynchronous operations.

`interval_map` implements an `IntervalMap` struct:
- It accepts `Interval<T>` as the key, where `T` can be any type that implements `Ord` trait. Therefore, intervals such as $[1, 2)$ and $["aaa", "bbb")$ are allowed
- The value can be of any type

`interval_map` supports `insert`, `delete`, and `iter` fns. Traversal is performed in the order of `Interval<T>` . For instance, with intervals of type `Interval<u32>`:
- $[1,4)<[2,5)$, because $1<2$
- $[1,4)<[1,5)$, because $4<5$

So the order of intervals in `IntervalMap` is $[1,4)<[1,5)<[2,5)$.

Currently, `interval_map` only supports half-open intervals, i.e., $[...,...)$.

## Benchmark

The benchmark was conducted on a platform with `AMD R7 7840H + DDR5 5600MHz`. The result are as follows:
1. Only insert
    | insert          | 100       | 1000      | 10, 000   | 100, 000  |
    | --------------- | --------- | --------- | --------- | --------- |
    | Time per insert | 5.4168 µs | 80.518 µs | 2.2823 ms | 36.528 ms |
2. Insert N and remove N
    | insert_and_remove  | 100       | 1000      | 10, 000   | 100, 000  |
    | ------------------ | --------- | --------- | --------- | --------- |
    | Time per operation | 10.333 µs | 223.43 µs | 4.9358 ms | 81.634 ms |

## TODO
- [] ~~Support for $(...,...)$, $[...,...]$ and $(...,...]$ interval types.~~ There's no way to support these interval type without performance loss now.
- [] ~~Add Point type for Interval~~ To support Point type, it should also support $[...,...]$, so it couldn't be supported now, either. But you could write code like this:
    ```rust
    use interval_map::{Interval, IntervalMap};

    impl Interval<u32> {
        // so a point X equals to [X, X + 1)
        fn new_point(x: u32) -> Self {
            Interval {
                low: x,
                high: x + 1,
            }
        }
    }

    #[test]
    fn test_insert_point() {
        let mut interval_map = IntervalMap::<u32, i32>::new();
        interval_map.insert(Interval::new_point(5), 10);
        interval_map.insert(Interval::new(3, 7), 20);
        interval_map.insert(Interval::new(2, 6), 15);

        assert_eq!(interval_map.get(&Interval::new_point(5)).unwrap(), &10);
        assert_eq!(
            interval_map.find_all_overlap(&Interval::new_point(5)).len(),
            3
        );
    }
    ```
- [x] Add more tests like [etcd](https://github.com/etcd-io/etcd/blob/main/pkg/adt/interval_tree_test.go)
- [x] Refine iter mod