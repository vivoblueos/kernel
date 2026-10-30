extern crate criterion;
extern crate gcd;
extern crate rand;
extern crate rand_chacha;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use gcd::Gcd;
use rand::{Rng, SeedableRng};

const SEED: u64 = 314;

fn criterion_benchmark(c: &mut Criterion) {
    macro_rules! bench_function {
        ($name:expr, $type:ty, $func:ident) => {
            c.bench_function($name, |b| {
                let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(SEED);
                let values: Vec<$type> = (0..1000).map(|_| rng.gen()).collect();
                b.iter(|| {
                    for i in 0..values.len() - 1 {
                        let (a, b) = (values[i], values[i + 1]);
                        black_box(a.$func(b));
                    }
                })
            });
        };
    }

    bench_function!("gcd euclid u8", u8, gcd_euclid);
    bench_function!("gcd euclid u16", u16, gcd_euclid);
    bench_function!("gcd euclid u32", u32, gcd_euclid);
    bench_function!("gcd euclid u64", u64, gcd_euclid);
    bench_function!("gcd euclid u128", u128, gcd_euclid);

    bench_function!("gcd binary u8", u8, gcd_binary);
    bench_function!("gcd binary u16", u16, gcd_binary);
    bench_function!("gcd binary u32", u32, gcd_binary);
    bench_function!("gcd binary u64", u64, gcd_binary);
    bench_function!("gcd binary u128", u128, gcd_binary);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
