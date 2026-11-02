# Agent 11: exact second sparse-gateway criterion for BB(6) holdout C

**Status: kernel-checked intermediate research, not a machine classification or a BB(6) bound.**

Target machine: `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`. Its certified blank-entry accelerator starts at `(a,k,c)=(5,0,1)`. See [the upstream Lean proof](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC.lean). Our original uncompressed [CLine.lean](./CLine.lean) proves that its stopping condition is exactly reachability of `(0,2j,4j+10)`.

## Stronger exact equivalence

Theorem `BB6CLine.stops_iff_reset_or_side`, checked by Lean 4.36.0-rc2:

```text
(∃ s, Reach s ∧ nextC s=none)
  ↔ (∃ j ≥ 1, Reach (2*j+1,3*j+4,0))
     ∨ (∃ m ≥ 0, Reach (0,2*m,12*m+23)).
```

The first family is a set of zero-right-counter reset states satisfying `2k=3a+5`, with odd `a≥3`. The second is a zero-first-counter family with even `k`, satisfying `c=6k+23`. Both are exact all-time blank-entry targets. Neither has been proved globally unreachable or reachable, so this does **not** decide machine C or BB(6).

## Proof architecture

The accompanying Lean files prove these universal facts:

- `LowGate.lean`: any successful transition ending with middle counter zero has odd first counter. It rules out the lowest diagonal target `(0,0,10)` from the actual blank-start orbit.
- `BackGate.lean`: every transition into `(a,k,c)` with `k≥3,c≥4` must come from precisely `(a+1,k-1,c+1)`. A structural induction follows all such predecessor steps until the `k=2` boundary. A separate exact induction proves forward high-counter sweeps.
- `ResetGate.lean`: complete predecessor classification for the even-right-counter `k=2` boundary, and for the odd-right-counter `k=1` successor. The latter either comes from a `c=0` reset or an impossible `k=0,a` even state. The former either connects to that reset or comes from an even-`k), zero-`a` branch. Algebra gives exactly the two formulas above. The reverse direction constructs all finite forward transitions to the halt line.

The `#print axioms` audit for `stops_iff_reset_or_side` reports only `[propext, Classical.choice, Quot.sound]` with no `sorryAx`. Proofs refer to an independently copied exact accelerated map, whose source was compared with the upstream module. A standalone kernel-checked cross-module bridge has not yet been built.

## Source preservation and reproduction

The three source files are retained, unmodified, in `gates-lean.tar.xz.b64`, a checksum-verified xz-compressed tar archive. The source bundle is exactly 4088 base64 characters with SHA-256 `98a564526d624202b61bd37af38d231aa13fb563e7edae9453a8cfe7f8dba0dd` (excluding the final newline), and tar SHA-256 `8beac4d083a533ae8f1be5c2211de61bf771126ef2abf302580e08c74633ab24`.

Run `python reconstruct.py` in this directory (requires the `filelock` Python library). It validates the archive and every Lean source SHA-256 and materializes files using locked, atomic writes. Then compile successive source files into Lean object files in this order, with the directory on `LEAN_PATH`: `CLine.lean`, `LowGate.lean`, `BackGate.lean`, and finally `ResetGate.lean`. The proofs import only Lean-bundled `Std`; no Mathlib is required.

## Research target

Prove or disprove that both gateway families are absent from the reachable orbit. A natural next approach is to derive and check return maps for `c=0` and `a=0` sections, with explicit conditions on `2k-3a` and `c-6k`. Finite simulation to one billion macro steps found neither gateway, but finite non-hits cannot decide this question. For prior results see [Agent 8's Machine C investigation](../agent8-rank-barriers/README.md).
