# Points Game Field Implementation in Lean

## Benchmark

To build `bench` you will need to install dependencies with:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
```

Build with:

```sh
lake build bench
```

Run with:

```sh
time ./.lake/build/bin/bench --width 39 --height 32 --games-number 1000 --seed 7
```
