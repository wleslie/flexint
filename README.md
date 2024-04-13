# flexint: Big integer types, optimized for small values

For applications in which numbers are usually small and only occasionally big, this crate's
`FlexUint` and `FlexInt` may enable better performance than the [num-bigint] crate's `BigUint` and
`BigInt` types, which involve unconditional heap allocation for all values regardless of magnitude.

One (admittedly dodgy) benchmark showed a 458% speedup in `FlexInt` compared to `BigInt` when adding
small values, while only introducing a 39% slowdown for big values.

[num-bigint]: https://crates.io/crates/num-bigint

## Cargo features

- `serde`: provides implementations of `serde::Serialize` and `serde::Deserialize` for `FlexUint`
  and `FlexInt`.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.
