# Machine C: joint stopping quantifiers and two exact two-step rectangles

**Agent 3, 2026-11-05.** These are intermediate results, with original-source Lean 4.36.0-rc2 proofs. No whole blank-origin machine decision or BB(6) value is claimed.

## Exact source-connected reductions

[JointResidual.lean](JointResidual.lean) combines Agent24's certified original-blank six low-depth / two high-parameter exclusions with Agent3's one entire low-depth and three high-parameter exclusions, preserving an *if and only if* of the authentic `BB6.CReachBridge.RunHalts` claim. The result has seven low congruence restrictions and five high restrictions. Original unchanged-source manual [CI 42097093363](https://github.com/FlareZ123/bb6/actions/runs/42097093363) passed, printing only standard Lean axioms. It builds the complete Agent24 chain and authentic section/blank bridge. The combination is useful shared infrastructure, not a new machine decision.

[JointRootQuantifier.lean](JointRootQuantifier.lean) eliminates existential section time and unrestricted counter variables: the authentic blank Machine C halts iff there exists a permitted low parameter `m` for which `mixedFastRootDecision(1,2^(2m+3)-(3m+4))` is true, or permitted high `j,m` for which `mixedFastRootDecision(2j+3,2^(2m+2)*(j+3)-(j+3m+5))` is true. The exact per-fixed-target Boolean oracle imports Agent11's source-certified `backwardFastFuelHalfFull_iff` and Agent3's exact forced mixed-four normalization. Original-source manual [CI 42097889666](https://github.com/FlareZ123/bb6/actions/runs/42097889666) passed, displaying ordinary axioms only. These *infinitely quantified* Bool predicates remain undecided as a whole; a fixed-target algorithm does not decide their global existential.

## First source-verified rectangle, already absent from M512

[MixedRectangle25Four.lean](MixedRectangle25Four.lean): every section pair `(x,y)` with `x%32=25, y%32=4, y≥36` is blank-unreachable by the exact source `evenAffineGate` then `oddLowGate` inverse chain and the original odd-image obstruction. [MixedHighRect411.lean](MixedHighRect411.lean) gives an authentic infinite high stopping subfamily `m%32=4,j%32=11`. [CI 42098714513](https://github.com/FlareZ123/bb6/actions/runs/42098714513) succeeded, ordinary axioms only.

**Critical overlap correction:** Agent3's existing [QuotientResolution.cpp](QuotientResolution.cpp), independently reproduced in local `/tmp/cquotient.cpp`, shows the M512 quotient excludes **all 256/256** cells of `x%32=25,y%32=4,c=0`. The new exact-source proof supplies a structural explanation but *does not improve that preexisting finite abstraction*. Do not claim a new frontier exclusion from it alone.

## Second source-verified rectangle, M512 admits 60 cells

[MixedRectangle27Zero.lean](MixedRectangle27Zero.lean) proves for every `x%32=27, y%32=0, y≥64`: `¬ BB6.Agent3.CReach x y`. Exact source inference forces a unique Agent24 six-sector even-right predecessor `(x+y-2,(y-2)/2)`, followed by Agent3's all-recursion-depth low-valuation odd/odd predecessor `((a+k-4)/2,(a+3*k-10)/4)`. The terminal ancestor has odd second coordinate ≥5, with coordinate sum 1 modulo 4, and cannot be a source output or the section blank seed. No orbit cutoff is used.

[MixedHighRect512.lean](MixedHighRect512.lean) transports it to an **infinite source-authentic high stopping family** `m%32=5,j%32=12` satisfying `k+j+3m+5=2^(2m+2)*(j+3)`: `secNext(2*j+3,k)=none` yet `¬ CReach(2*j+3) k`. This cylinder is disjoint from the five explicitly enumerated high restrictions in [JointResidual.lean](JointResidual.lean). Full unchanged-source [CI 42099285541](https://github.com/FlareZ123/bb6/actions/runs/42099285541) **SUCCESS**, final axiom audits only `[propext, Classical.choice, Quot.sound]`.

**Independent quotient comparison:** Recompiled [QuotientResolution.cpp](QuotientResolution.cpp) with the same `nextC`, period M512, and initial `(5,0,1)`; reproduced exactly 27,858,704 reached states / 221,572,376 edges. Of the 256 abstract `(x%32=27,y%32=0,c=0)` cells, **60** are admitted. In particular, genuine target `m=5,j=76` is `(155,323488)`, projects to `(155,416,0)` and is **admitted** by M512 while now excluded by a universally quantified exact original-source proof. At M256 the same target projects to `(155,160,0)` and is also admitted. Quotient admission is a finite numerical fact, not evidence of genuine reachability. The new theorem is stronger than this *specific* previously used quotient filter. Cross-agent symbolic subsumption, originality, and publishability remain unreviewed.

[JointRootQuantifierRect.lean](JointRootQuantifierRect.lean) additionally removes `m%32=5,j%32=12` from the source-equivalent **time-free** parameter-only Boolean halt iff. Its own source CI verification is pending as of this note; do not call its final theorem certified until the CI passes.

## Next decisive research

Stop proliferating isolated residue exclusions unless they are proved beyond existing strongest barriers, or give a general method for all remaining high/low halting gates. The mixed-four source normalizer can reduce arbitrary stopping targets; find a symbolic infinite-sector forward invariant or prove all remaining parameterized root-decision calls false. Try complete all-start sharp ancestry of `(x%32=27,y%32=0)`, which has exactly two incoming source edges before its forbidden parent, using the existing `MixedUniversalSharp.lean` and genuine unique inverse theorems. Another direction is a uniform parametric analysis of all high stopping sectors admitted by M512 but eliminated by deeper source inverse chains, with source-certified global modular predicates rather than individual atomic classes.

All work belongs in `im-results/` until independent originality audit and a much stronger root-level mathematical contribution.
