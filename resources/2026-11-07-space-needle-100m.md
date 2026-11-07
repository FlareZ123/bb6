# Space Needle 100-million-term computation

**Retrieved:** 2026-11-07  
**External repository:** [oohzaim1-afk/space-needle-100M](https://github.com/oohzaim1-afk/space-needle-100M)  
**Inspected main-tree commit:** `96e50a6ad829fa43e4ecfdf881b6679e599ef0b4`  
**Machine:** `1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD` (Space Needle, BB(6), BMO problem 6)

## Result and indexing

The repository reports an exact-integer computation of the reduced sequence

```text
b₀ = 6
bₙ₊₁ = bₙ + v₂(bₙ) + 3/2 · (bₙ / 2^v₂(bₙ) − 1)
halt iff bₙ is a power of two
```

through 100,000,000 updates. No power of two was encountered. The maximum observed 2-adic valuation is 25, first attained at 1-based term position 23,145,881. The final term has 94,125,050 bits (28,334,464 decimal digits).

The local formalization starts at high-level state `N 1`, with counter `d). Its shifted variable is `b=d+2`, initially 3. The first high-level transition sends `d=1` to `d=4), hence `b=6`. The external run starts at this first post-start value 6. Its initial value 3 is not a power of two, so the omitted initial check is trivial. The external run checks positions 1 through 100,000,001, including the term after the 100,000,000th update.

## Independent computation and anchors

The external README records:

- C + GMP computation of 100,000,000 updates, with 400 checkpoints at 250,000-update intervals.
- Rust `num-bigint` cross-check through 23,250,000 terms; 93 overlapping checkpoints matched the C+GMP implementation, with zero mismatches.
- A separate Python standard-library big-integer implementation through 1,000,000 terms, matching the published prefix and the 1,000,000-term bit length.
- A block-affine re-derivation of the full 100,000,000-term range, matching all 400 checkpoints, all 13 valuation-record events, and the final term.
- The published final integer in `data/final_term_100M.bin`, canonical big-endian minimal-byte encoding, SHA-256:
  `627e09c5bb1fbf93fe18ed3f2a2feaff45a16f139282364e07831337766acce1`.
- Checkpoint hashes in `data/sha256_checkpoints_100M.csv`; the C+GMP checkpoint CSV hash is `2dd4c88d169f5db331598d49a7773504a18f6dd621d15482f9b497915adb3169`.

Primary evidence files in the external repository:

- [README and reproduction instructions](https://github.com/oohzaim1-afk/space-needle-100M/blob/96e50a6ad829fa43e4ecfdf881b6679e599ef0b4/README.md)
- [C+GMP source](https://github.com/oohzaim1-afk/space-needle-100M/blob/96e50a6ad829fa43e4ecfdf881b6679e599ef0b4/code/bb6gmp.c)
- [Rust source](https://github.com/oohzaim1-afk/space-needle-100M/blob/96e50a6ad829fa43e4ecfdf881b6679e599ef0b4/code/bb6tools_main.rs)
- [Block-affine independent implementation](https://github.com/oohzaim1-afk/space-needle-100M/blob/96e50a6ad829fa43e4ecfdf881b6679e599ef0b4/code/bb6blocks.py)
- [C/Rust checkpoint comparison](https://github.com/oohzaim1-afk/space-needle-100M/blob/96e50a6ad829fa43e4ecfdf881b6679e599ef0b4/data/crosscheck_C_vs_Rust.txt)
- [Full-range block re-derivation report](https://github.com/oohzaim1-afk/space-needle-100M/blob/96e50a6ad829fa43e4ecfdf881b6679e599ef0b4/data/block_100M_run_info.txt)
- [Final integer hash record](https://github.com/oohzaim1-afk/space-needle-100M/blob/96e50a6ad829fa43e4ecfdf881b6679e599ef0b4/data/final_term_100M.sha256)

## Mathematical results included in the external package

The `laws/` directory contains exact macro-transition step-count laws L0–L4, a closed-form halting time for the synthetic family `(2^k−3,c)`, and a modular obstruction classification. The package marks L1 and L3 as formally proven and machine-certified, while L4 remains empirical. Its modular report states that 96 of the 120 valuation classes (a\leq120) are obstructed and 24 admissible; the classification is supported by its Python factorization, subgroup-membership, CRT, and brute-force checkers, rather than by a Lean proof in that package.

The report lists four elementary infinite obstruction progressions:
`a ≡ 4 (mod 20)`, `a ≡ 19 (mod 21)`, `a ≡ 62 (mod 110)`, and `a ≡ 21 (mod 156)`. The local Space Needle development already formalizes the first two. Agent 48's new `SpaceNeedleObstructionFamilies.lean` formalizes the latter two and adds progressions `a ≡ 201 (mod 342)` (modulus 19) and `a ≡ 74 (mod 812)` (modulus 29).

## Evidential limits

This is strong reproducible computational evidence over a finite prefix, not a proof that the Space Needle machine never halts. The external README explicitly states that the 100M run is a record and statistical study, not a proof or a resolution of the halting question. It does not establish a BB(6) upper bound or determine BB(6).

The external package declares MIT licensing for code and CC-BY-4.0 for data, logs, and text. This note links to the original artifacts rather than copying the large final integer or datasets.
