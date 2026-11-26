# Raw55 D1 sibling: source-checked first-hole refinement

**Parent:** `1RB---_1RC---_0RD---_1LD0RE_------_------`, the D1=0RE sibling of the authentic first-one cylinder. The parent has seven undefined transitions.

## First-hole partition

The existing translated-cycle/canonical-cut classifier, run with cap 1000, lookback 32 and split depth 2, gives:

| Leaf type | Count |
|---|---:|
| Translated-cycle leaves | 233 |
| Explicit unresolved five-hole cylinders | 274 |
| Split nodes | 22 |
| Last-hole leaves | 0 |
| Canonical aliases | 0 |

The root split occurs at live time 6 on E1. The maximum first-hole query time is 12 and the maximum cycle-end index reported by the classifier is 48. The full tree is `Raw55-cut.json`; the complete open complement is `Raw55-open.txt`.

The classifier is the existing `im-results/agent7-raw49/cut.cpp`, not a new simulation semantics. Its V8 port reproduced the Raw47 reference tree and open list byte-for-byte before being applied to Raw55. The pinned CI run independently reproduced the Raw55 C++ counts and checked the committed JSON/open data exactly. This computational preflight is supporting evidence; the Lean theorem below is the mathematical result.

## Source-checked local theorem

`Raw55Cut.lean` is generated from `Raw55Cut.template` by `generate.py`. It instantiates the original-source `CanonicalPartial` audit for the exact parent and tree. The theorem `BB6.Agent25Raw55Cut.canonical_local_sound` states that every TNF-quotient-compatible completion is either bounded by weighted score 7014 or belongs to one of the 274 explicit residual cylinders. The companion `canonical_local_sound_84` gives a stronger root-compatible conditional refinement.

The Raw55 cut module compiled under pinned Lean 4.36.0-rc2 in run 45876194466; its printed axiom profile was standard Lean only. The overall first attempt failed in the then-current roster wrapper, not in the Raw55 cut module.

## Roster consumers

**Legacy auxiliary:** `Raw55Agent31LegacyGraft.lean` passed pinned Lean CI run 45876672004. It proves exact membership in the older 124-entry Agent31 root roster and replaces that one entry by the 274 residuals, yielding 123 unchanged entries plus 274 children (397 total). This is a valid historical source-checked refinement, but it is not the current global frontier.

**Current global consumer:** the relevant frontier is `BB6.Agent3Canonical64Raw120.roster64` with `sound64_integrated`. `Raw55Canonical64Graft.lean` tests exact membership in that 64-entry roster and uses the quotient-to-quotient `graftRoster` composition pattern. If the membership count is exactly one, it replaces one entry by the 274 Raw55 residuals, yielding 63 unchanged entries plus 274 leaves (337 total). The local 7014 bound is lifted to the common 6,766,859 floor. This is a strict refinement, not a net reduction in residual count.

The first Canonical64 attempt failed before Lean elaboration because `Raw66Data` was absent from the indexed source roots. The existing Agent10 source generator `python im-results/agent10-tnf-multipump/generate.py 66 70 80` has been added to the Raw55 target. Retry run 45877676615 is the current acceptance attempt. The exact Canonical64 membership result is not yet established; if the gate is not one, no global-frontier refinement is claimed.

## Reproduction

```bash
g++ -std=c++20 -O3 im-results/agent7-raw49/cut.cpp -o /tmp/raw55-cut
/tmp/raw55-cut '1RB---_1RC---_0RD---_1LD0RE_------_------' 1000 32 2 /tmp/raw55
cmp /tmp/raw55.json im-results/agent25-raw55/Raw55-cut.json
cmp /tmp/raw55.open im-results/agent25-raw55/Raw55-open.txt
python im-results/agent25-raw55/generate.py
python im-results/agent31-three-hole-tnf/generate_sweeps.py
python im-results/agent31-three-hole-tnf/generate_four_hole.py
python im-results/agent10-tnf-multipump/generate.py 66 70 80
python tools/lean_compile_closure.py --workdir /tmp/raw55-source --jobs 4 im-results/agent25-raw55/Raw55Canonical64Graft.lean
```

The Raw47 five-state FAR search certified 0/114 leaves, so its identical FAR5 search was not repeated on Raw55. The 274 residuals remain explicit hypotheses. This is not a complete Raw55 parent Cover or a BB(6) upper bound.
