# Counted-prefix left-output seed windows

This note isolates the only residue-dependent part of the full left-output proof: the tape immediately before the common `carryFinishFromD` suffix. It is an intermediate proof plan, not a verified Lean theorem.

The target is the canonical output bit
```lean
carryLeftOutputBit r T x :=
  if x < -3*(r:Int)-2 then T x
  else if x ≤ -3*(r:Int) then true
  else decide (x % 3 = 1)
```
For each long residue branch, the seed obligation is `∀ x, x < hB → T2 x = carryLeftOutputBit r T x`. The finish theorem then handles the rest, because its final tape is
`if x < hB then T2 x else decide ((x-hB)%3=0)`.

| r | left-sweep head h' | finish head hB | nR | special input cell | finite bridge window needed for hseed |
|---|---:|---:|---:|---:|---|
| 4k, k>0 | -12k | h'+10 | 4(k-1) | h'-2 | bridge0 offsets -1..9 |
| 4k+1, k>0 | -12k | h'+10 | 4(k-1) | h'-5 | bridge3 offsets -4,-3; AD12 offsets -2..9 |
| 4k+2 | -12k-4 | h'+2 | 4k | h'-4 | bridge2 offsets -3..1 |
| 4k+3 | -12k-8 | h'+6 | 4k | h'-3 | bridge1 offsets -2..5 |

All branches satisfy `hB+3*nR=-2` and `hB % 3 = 1`, so the same `carryFinishFromD` output formula applies.

## Far-left and special-cell decomposition

- **r=4k:** for `x<h'-2`, both the bridge frame and its right suffix are outside and the left sweep preserves x. At `x=h'-2=-3r-2`, use the special `carryInputBit` cell. The bridge0 frame handles `h'-1..h'+9`.
- **r=4k+1, k>0:** for `x<h'-5`, both bridge3 and AD12 are outside and the left sweep preserves x. At `x=h'-5=-3r-2`, use the special input bit. Bridge3 writes ones at `h'-4,h'-3`; AD12 writes the every-third pattern from `h'-2) through `h'+9`.
- **r=4k+2:** for `x<h'-4`, bridge2 is outside and the left sweep preserves x. At `x=h'-4=-3r-2`, use the special input bit. Bridge2's final frame covers relative offsets -3..2; the seed only needs -3..1 because hB=h'+2.
- **r=4k+3:** for `x<h'-3`, bridge1 is outside and the left sweep preserves x. At `x=h'-3=-3r-2`, use the special input bit. Bridge1's final frame covers relative offsets -2..6; the seed only needs -2..5 because hB=h'+6.

The exceptional `r=1) short branch is already handled separately by Agent 24's additional left-output conjunct on `carryShortPrefix_r1`.

## Frame-cell lemmas

`FrameCellLemmas.lean` records exact finite-cell patterns for:
- bridge0: true at offsets -1,0; then offsets congruent to 1 mod 3;
- bridge1: true through offset 0; then offsets congruent to 0 mod 3;
- bridge2: true through offset -2; then offsets congruent to 2 mod 3;
- bridge3: true at offsets -4,-3;
- AD12: offsets 0,3,6,9,12.

The frame-level corollaries translate these local patterns to absolute tape coordinates under the appropriate head congruence. They are **not yet Lean-compiled** in this invocation. A future proof should import this helper module, discharge the far-left preservation and special input cell once per branch, and use the frame lemmas for the bounded window rather than repeating long `simp` expansions.
