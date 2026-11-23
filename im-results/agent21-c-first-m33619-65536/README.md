# Machine C: a new 13-ray inverse trap in the surviving low-stopping sector

**Original-source Lean 4.36.0-rc2 verified, 23 November 2026.** The complete source proof passed [manual CI run 45113896118](https://github.com/FlareZ123/bb6/actions/runs/45113896118), including the copied-criterion definitional bridge and the full stopping-index theorem, without `sorry`/`admit`. Standard Lean logical axioms only. This does **not** decide Machine C or BB(6).

## New all-parameter mathematical obstruction

Write `F = BB6.Agent46.secNext`, the original two-counter Machine C return map from the true blank-section root `(5,1)`. The intended original-source theorem is

```lean
∀ time u : Nat,
  BB6.Agent8Section.run F time (some (5,1)) ≠
    some (1,65536*u+30211)
```

The original Machine C first-family stopping equation is

```text
k + 3*m + 4 = 2^(2*m+3).
```

For every `m ≡ 33619 (mod 65536)`, its right counter satisfies `k ≡ 30211 (mod 65536)`; hence this infinite stopping-index progression is forbidden. It belongs to the previously unresolved `m ≡ 851 (mod 2048)` sector. It is disjoint from Agent 21's prior `m ≡ 1875 (mod 2048)` exclusion and the previously certified `m ≡ 6995 (mod 8192)` subfamily.

## Exhaustive infinite inverse tree

Every pair below is an affine function of an **arbitrary natural** `u`. The arrows list **every possible** original section predecessor of each target, not merely one sampled parent. All right counters are at least 10,341, so the existing source-exact `complete_section_inverse` iff theorem applies without any small-output exception.

| Tag | First counter | Second counter | All possible immediate predecessors |
| --- | ---: | ---: | --- |
| R | 1 | 65536u+30211 | P |
| P | 32768u+15104 | 49152u+22656 | A, B1, B2, B3 |
| A | 81920u+37758 | 24576u+11327 | none |
| B1 | 20480u+9438 | 55296u+25484 | C1 |
| B2 | 5120u+2358 | 62976u+29021 | C2 |
| B3 | 1280u+588 | 64896u+29903 | C3 |
| C1 | 75776u+34920 | 27648u+12741 | none |
| C2 | 34048u+15687 | 48512u+22353 | D2 |
| C3 | 33088u+15243 | 48992u+22572 | D3a, D3b |
| D2 | 41280u+19018 | 44896u+20684 | E2 |
| D3a | 82080u+37813 | 24496u+11285 | none |
| D3b | 20520u+9451 | 55276u+25463 | none |
| E2 | 86176u+39700 | 22448u+10341 | none |

At each terminal node `y` is odd and `(x+y)%4∈{1,2}`. The complete original inverse grammar forbids these residues for any successful predecessor. The other edges follow by a complete case split on the source `a=0,1,≥2`, the direct branch and the arbitrary bounce depth `n`. For an affine target with sum valuation `v`, `2^n` divides either `x+y` or `x+y+1`; its congruence modulo `2^(v+1)` bounds `n≤v`. All remaining depth cases are settled as universal Presburger statements by Lean's `omega`, with no finite `u` cutoff.

The thirteen rays form a backward-closed set disjoint from `(5,1)`. Induction on arbitrary path length from the genuine blank root therefore excludes R at **every time**. The model's `PredAll` deliberately permits all transitions to outputs with `y<5`, so no small-return edge is accidentally lost.

## Reproducible proof artifacts and trust boundaries

- [`Low33619.lean.xz.b64`](Low33619.lean.xz.b64) is the complete 605-line abstract Lean proof, compressed as xz/base64. Decode by `base64 -d Low33619.lean.xz.b64 | xz -d > Low33619.lean`. Decoded SHA-256 is `2c3dd399810da73c658434fb1ac91b3c831c55d7069d3df629cad1cae8e7cc29`. It includes the original inverse predicate literally, all 13-ray fan lemmas, the backward-closed induction and the generic all-time `runF_no_33619` theorem.
- [`Low33619Source.lean`](Low33619Source.lean) imports unchanged source `BB6.Agent46.secNext` and its already source-certified `complete_section_inverse`, establishes definitional agreement with the abstract predicate, and derives `blank_no_33619_low` and `first_stop_m33619_mod65536`.
- The pre-existing [manual-only original-source workflow](../../.github/workflows/agent21-low1875-source.yml) was extended, rather than creating a new CI workflow. It SHA-256-checks the decoded source, compiles all original dependencies and prints final axioms.

**Research boundary:** this is one infinite parameter progression, not a complete low-gate exclusion, a full Machine C decision or a universal Busy Beaver upper bound. External novelty and implication by substantially broader existing orbit theorems remain unreviewed. The valuable next direction is to automate this affine preimage-closure method and attack other surviving `m%2048` classes without duplicating prior certified progressions.
