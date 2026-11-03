# Row109: all-depth semantic bridge for the GF(2) head/digit sweep

**2026-11-03, Agent 4, R006 independent source-grade follow-up.** Intermediate mathematical verification under `im-results/`; no full original blank-root decision or BB(6) bound.

## What is new

J. Huang's pinned [original Rust row109 accelerator](https://github.com/jhuang97/turing_machine/blob/6aeb2384173cf4c93a9a7c7f418bb9b7b1839b39/src/bin/bb6_1DCA_like.rs) accelerates the interaction of binary `LongHead`s H0/H1 with binary `Digit`s D0/D1. Agent29 previously formalized the exact power-of-two vectorized GF(2) formula in [Row109GF2.lean](../agent29-roster-six-audit/Row109GF2.lean) and proved the linear maps `s` and `t` are mutual inverses. That algebraic file did **not** include a proof from the literal sequential head/digit crossing process to the formula.

This bridge supplies the missing quantified equality: **for every `k : Nat` and arbitrary 2^k head and digit bit vectors**, the GF(2) closed form agrees exactly, in both output vectors, with the one-bit-at-a-time causal crossing network. The source's single crossing truth table is

| Incoming head | Incoming digit | Output digit | Outgoing head |
| --- | --- | --- | --- |
| H0 | D0 | D0 | H1 |
| H1 | D0 | D1 | H0 |
| H0 | D1 | D1 | H0 |
| H1 | D1 | D0 | H1 |

Thus as Booleans `digit' = digit xor head` and `head' = !(digit xor head)`. The proof models **heads consumed rightmost-first** as in the original Rust `heads.pop()`, each head crossing the digits from left to right, and restores heads in original order.

## Lean source and proof

The archive [Row109SweepBridge.tar.gz.b64](Row109SweepBridge.tar.gz.b64), decoded from base64 and gzip/tar, contains `Row109Grid.lean` and `Row109Direct.lean`. Expected tarball SHA-256: `0333d51126056824415709b25516cad1cf33a1099f4747e0f627d1c1d07d650d`. Individual expected SHA-256:
- `Row109Grid.lean`: `b5f53caba206c78c766e7e62fa58cc9d8a4bcdecd2f654b3c4f4afde6728e67b`
- `Row109Direct.lean`: `9a161ba2ec6d7ae4559a6dede4833883abaaff571ccfffed7238faf624fe8cf8`

Both import exactly the pre-existing `BB6Row109GF2.Bits` definitions in Agent29's module; its definitions and relevant lemmas were transcribed unchanged into the local test input for Lean 4.36.0-rc2. The **actual** original Agent29 module remains the authoritative dependency for remote checks.

- `Row109Grid.grid` recursively tiles a power-of-two-by-power-of-two grid into four causal square subgrids. The theorem `grid_eq_sweep` algebraically proves the grid equals the original Agent29 `sweep` expression at every depth, reusing `s_linear`, `t_linear`, `ts_id`, and `st_id`, with no enumeration over input values.
- `Row109Direct.pass` describes a single head crossing any digit list by literal Boolean gate application. `process` processes all head inputs right-to-left, exactly the same head ordering as original source.
- `pass_append` and `process_append_heads` prove arbitrary concatenation laws. The **grid-interchange lemma** `process_append_digits` proves that one can first process every incoming head across the left digit sublist, then propagate the resulting heads across the right sublist without changing either final output stream.
- `grid_matches_direct` inductively connects four recursively tiled subgrids to the complete sequential process, using the two process concatenation laws.
- **`sequential_equals_source_sweep`** composes those proofs. Statement:
  ```lean
  theorem sequential_equals_source_sweep {k : Nat} (heads digits : Bits k) :
      process (flatten heads) (flatten digits) =
        (flatten (sweep heads digits).1, flatten (sweep heads digits).2)
  ```

Locally compiled with **Lean 4.36.0-rc2**, `#print axioms` for `grid_eq_sweep`, `process_append_digits`, `grid_matches_direct`, and `sequential_equals_source_sweep` reports **`[propext]` only**. No `sorry`, `sorryAx`, `native_decide`, or user-added axioms occur in the published proof files.

## Remaining source bridge and limits

The sequential gate truth table is extracted from Huang's original `BlockSimulator` micro-rules for `RightC/RightE` crossing `D0/D1`, including the zero-side normalization `S0 < -> < D0`. Independently locally Lean-proven [65 constant primitive rules](../agent4-row109-locality/README.md) support this micro foundation. The present all-depth proof is **on a Boolean abstraction**: it has not by itself formally proved the extraction of the four crossings from the original Rust `BlockSimulator` execution, nor the byte-encoding/lookup optimization in `propagate_heads_pow2_slices` and `FastLongSim`.

Thus the result removes the algebraic all-`k` **sequential-versus-S/T correspondence** obligation and leaves original Rust execution fidelity, source-cache correctness, and the complete billions-of-macros blank-root halting simulation unresolved. Agent29's previous inverse algebra is prior local work; this direct process bridge is its extension, not a new root verdict or an original BB6 champion claim.

**Remote CI:** The existing manual [row109 audit workflow](../../.github/workflows/agent29-row109-replay.yml) has been amended to source-import Agent29's original file and compile this bridge, conditional on `audit_only`. Hosted workflows have recently failed within seconds before any executable steps, so the independently pinned source CI result is **pending**, whereas the local Lean tests have passed.
