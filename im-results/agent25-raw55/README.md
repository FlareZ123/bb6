# Raw55 D1 sibling: source-audited first-hole cut

**Parent:** `1RB---_1RC---_0RD---_1LD0RE_------_------`, the D1=0RE sibling of the authentic first-one cylinder. Its seven undefined transitions are retained as a seven-hole parent.

## Current mathematical statement

A bounded translated-cycle / canonical first-hole preflight with cap 1000, lookback 32 and split depth 2 yields 233 translated-cycle leaves, 274 explicit unresolved five-hole cylinders, 22 split nodes, zero last-hole leaves and zero canonical aliases. The root split occurs at live time 6 on E1; the maximum first-hole query time is 12 and the maximum cycle-end index reported by the classifier is 48. The 274 unmatched cylinders are preserved verbatim in `Raw55-open.txt`; the complete tree is `Raw55-cut.json`.

The classifier is the existing `im-results/agent7-raw49/cut.cpp`, not a new simulation semantics. Its V8 port reproduced the full Raw47 reference tree and open-list byte-for-byte before being applied to Raw55. This is computational preflight evidence, not a theorem.

## Intended Lean result

`Raw55Cut.lean` is generated from `Raw55Cut.template` by `generate.py`. It instantiates the original-source `CanonicalPartial` audit for the exact parent and tree. The intended theorem `BB6.Agent25Raw55Cut.canonical_local_sound` states that every TNF-quotient-compatible completion is either bounded by weighted score 7014 or belongs to one of the 274 explicit residual cylinders. A companion 84-bound statement gives a stronger root-compatible conditional refinement.

**Acceptance status:** the source theorem has not yet passed the repository's pinned Lean 4.36.0-rc2 original-source closure. Until that audit succeeds, the partition remains computational evidence. Even after acceptance, it is a strict refinement, not a complete Raw55 parent Cover: all 274 residuals remain hypotheses. No Canonical64 roster decrement or BB(6) upper bound is claimed.

## Reproduction and next step

```bash
g++ -std=c++20 -O3 im-results/agent7-raw49/cut.cpp -o /tmp/raw55-cut
/tmp/raw55-cut '1RB---_1RC---_0RD---_1LD0RE_------_------' 1000 32 2 /tmp/raw55
cmp /tmp/raw55.json im-results/agent25-raw55/Raw55-cut.json
cmp /tmp/raw55.open im-results/agent25-raw55/Raw55-open.txt
python im-results/agent25-raw55/generate.py
python tools/lean_compile_closure.py --workdir /tmp/raw55-source --jobs 4 im-results/agent25-raw55/Raw55Cut.lean
```

Use the existing manual Agent13 rootsibling workflow for source acceptance; do not add a workflow file. The final source theorem must retain the complete 274-element complement and pass the configured standard-axiom audit before any global parent integration.
