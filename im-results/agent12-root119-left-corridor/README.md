# Authentic #119 auxiliary B/0 left- and right-corridor first returns

**Mathematical scope:** Three unbounded, exact primitive-step return laws for the literal auxiliary six-state machine `1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD` on an arbitrary signed infinite physical tape. These are **conditional physical-tape theorems**, independent of the blank-root reachability of their input configurations. The historical #119 blank-start halt/nonhalt decision and BB(6) remain open.

**Proof status:** [Source-certified manual Lean CI 42586391176](https://github.com/FlareZ123/bb6/actions/runs/42586391176) successfully compiled unchanged repository `Root119Gate.lean`, `Root119BShift.lean`, and the new complete module, in Lean 4.36.0-rc2 with final theorem axiom reports containing only standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`. The new module is in [Root119Corridor.lean.xz.b64](Root119Corridor.lean.xz.b64), a base64-encoded XZ archive of exactly one original-source-import Lean module; decoded SHA-256 `65efa8844d8836f2579e4d7d5a71f308a2fc2f5343a0c0309f1f0c971ca2ab1d`. The [manual workflow](../../.github/workflows/agent12-root119-corridor.yml) checks this checksum, source import, compilation, and axiom audits.

## The three return laws

Let `c=(B,h,t)` with `t(h)=0` and `n ∈ ℕ`. The proofs concern true primitive instructions of the exact auxiliary transition table and arbitrary exterior tape, with no limit on `n`.

1. **First left gateway** (`left_gateway_return`): the left seven-bit suffix `t(h−7..h−1) = 0100111` (nearest six bits `100111`); its exact extra left-corridor condition has `t(h−8−2i)=1, t(h−9−2i)=0` for `0≤i<n`, ending `t(h−8−2n)=0`. The machine returns after **`14+2n`** primitive instructions to state B/0 at **`h−8−2n`**, with tape `t'(x)=t(x)` for every `x≤h−8−2n`.

2. **Second left gateway** (`left_gateway_B_return`): the left seven-bit suffix is `0101001` (nearest six bits `101001`), including the necessary left sentinel zero at `h−7`. It has the same alternating extended corridor as above. The return duration and head coordinate are identical to the first gateway, and the same left-boundary tape-preservation theorem holds.

3. **Right gateway** (`right_gateway_return`): `t(h−3..h−1)=000`, `t(h+1..h+2n)=1^(2n)`, and two right sentinels `t(h+2n+1)=t(h+2n+2)=0`. After exactly **`12+2n`** primitive instructions, the machine returns to B/0 at **`h+2n+2`**, preserving `t'(x)=t(x)` for every `x≥h+2n+2`.

The proofs first certify exact finite entry prefixes (12 steps for either left gateway, 6 for the right), then prove exact two-instruction recursive corridors by induction, including tape writes and endpoint symbols. Their source does not assume any finite simulation outcome, unbounded induction hypothesis about blank-run behavior, or unspecified external tape.

## Connection to the authentic blank trace and open quantifier

The repository's prior ten-million-step physical replay recorded 22,983 completed B/0 intervals. Its [Agent42 two-wave audit](../agent42-root119-guard/README.md) classified 22,934 of them and left **49** intervals under `other`. A fresh independent C++ replay of the literal six original rows identified local input patterns among those 49: 19 first-left, 10 second-left and 18 right gateways, and compared the resulting actual primitive duration and return-head displacement to the all-parameter formulas above. Each matched, accounting for **47 of 49** residual intervals. The remaining **two** begin with nearest left-six bits `101010` and are not covered by these theorems. The 10M classification is **finite numerical observation**; it is separate from the three all-parameter source proofs.

All three theorems permit arbitrary exterior tape, but require their input patterns. There is **no proof** that the true blank run is forever covered by these and prior return families. Even classifying every observed return within ten million steps would not decide the infinite blank-root orbit; in addition, avoiding the auxiliary fatal gate requires an all-time history-sensitive shield. The relevant existing exact gate and conditional shield theory is [Agent42's primary dossier](../agent42-root119-guard/README.md), with the underlying necessary-and-sufficient physical gate in [Agent3's inverse dossier](../agent3-root119-inverse/README.md). Original #119 transfers from the auxiliary via an externally published equivalence that must be tracked separately.

## Best next proof

A useful advance is a **single all-time forward-closed class** of genuine reachable B/0 configurations, including the two remaining `101010` branches and the rightward gateway, equipped with proof that the fatal `1100` left-of-head factor does not arise. A stronger initial target is preservation of the existing `NoLeft4 true true false` shield under the three source-certified corridors when their input patterns hold. Neither endpoint classification nor shield preservation alone establishes all-time blank-root closure.

## Reproduction

The exact `workflow_dispatch` action [agent12-root119-corridor.yml](../../.github/workflows/agent12-root119-corridor.yml) checks source integrity and compiles the underlying original physical-machine definitions. The source module intentionally imports the existing `Root119BShift` and uses its `run`/ `run_add`, with no reconstructed or reinterpreted transition table. Success run [42586391176](https://github.com/FlareZ123/bb6/actions/runs/42586391176).
