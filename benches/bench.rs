use std::hint::black_box;

use criterion::{criterion_group, criterion_main, Criterion};
use flexint::FlexInt;
use num_bigint::BigInt;

criterion_main!(bench_group);
criterion_group!(bench_group, add_small, add_big);

const A: i64 = -1216154675;
const B: i64 = 1304858009;

fn add_small(criterion: &mut Criterion) {
    criterion.bench_function("add_small_small", |bencher| {
        let a = A;
        let b = B;
        bencher.iter(|| black_box(&a) + black_box(&b));
    });
    criterion.bench_function("add_smallbig_small", |bencher| {
        let a = BigInt::from(A);
        let b = B;
        bencher.iter(|| black_box(&a) + black_box(&b));
    });
    criterion.bench_function("add_smallbig_smallbig", |bencher| {
        let a = BigInt::from(A);
        let b = BigInt::from(B);
        bencher.iter(|| black_box(&a) + black_box(&b));
    });

    criterion.bench_function("add_smallflex_small", |bencher| {
        let a = FlexInt::from(A);
        let b = B;
        bencher.iter(|| black_box(&a) + black_box(&b));
    });
    criterion.bench_function("add_smallflex_smallbig", |bencher| {
        let a = FlexInt::from(A);
        let b = BigInt::from(B);
        bencher.iter(|| black_box(&a) + black_box(&b));
    });
    criterion.bench_function("add_smallflex_smallflex", |bencher| {
        let a = FlexInt::from(A);
        let b = FlexInt::from(B);
        bencher.iter(|| black_box(&a) + black_box(&b));
    });
}

fn add_big(criterion: &mut Criterion) {
    let a = BigInt::from(A).pow(15);
    let b = BigInt::from(B).pow(15);
    criterion.bench_function("add_bigbig_bigbig", |bencher| {
        bencher.iter(|| black_box(&a) + black_box(&b));
    });
    let a = FlexInt::from(a);
    criterion.bench_function("add_bigflex_bigbig", |bencher| {
        bencher.iter(|| black_box(&a) + black_box(&b));
    });
    let b = FlexInt::from(b);
    criterion.bench_function("add_bigflex_bigflex", |bencher| {
        bencher.iter(|| black_box(&a) + black_box(&b));
    });
}
