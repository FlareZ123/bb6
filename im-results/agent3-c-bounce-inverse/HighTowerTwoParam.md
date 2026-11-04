# Machine C: two-dimensional unbounded-depth stopping tower excluded from the actual blank orbit

**Agent 3, 2026-11-04. Intermediate research.** This establishes an infinite parametric family of authentic Machine C immediate stopping inputs that is absent from the genuine blank-start *section* orbit. The overall Machine C halting problem and BB(6) remain open. The larger source-level theorem is in [HighTowerTwoParam.lean](./HighTowerTwoParam.lean). External novelty beyond this collaborative repository is not yet established, so this belongs in `im-results/`.

## Exact source-semantic claim

Define natural stopping indices `J(q,0)=64q+26` and `J(q,n+1)=16J(q,n)+42`. For every `q,n≥0`, let `a=2J(q,n)+3`, `k=15J(q,n)+40`. Then:

1. **Actual immediate stopping input.** `secNext (a,k)=none`, by the exact Agent15 source-verified second stopping parameter equation `k+J+3*1+5=2^(2*1+2)*(J+3)`.
2. **Unbounded exact forced inverse depth.** `BB6.Agent15.oddDepth k=4n+3`, with actual affine predecessor transitions at every one of these inverse steps.
3. **Closed normalized coordinates.** The complete genuine affine normalizer satisfies
   `affineNormalize a k=(32J-(240q+33+16n),120q+52)`.
4. **All-time actual blank nonreachability.** `¬ BB6.Agent15.CReach a k`, for all `q,n`. Both parameters independently index strictly increasing sequences of distinct stopping inputs.

The normalized pair has first coordinate `7 mod 8` and right coordinate `4 mod 8`, with right `≥52`. In [EvenChildSevenFour.lean](./EvenChildSevenFour.lean) we proved this entire infinite target cone has a unique genuine section predecessor `(x+y-2,(y-2)/2)`, and that predecessor cannot itself have *any* predecessor. This is a universal no-two-step ancestry theorem from **any** initial section state, independent of the blank seed. On the actual blank-start section, the first return is `(3,4)`, so no cone member can appear. The exact Agent15 source `reach_iff_normalize` transports the cone exclusion through every affine predecessor, regardless of inverse depth.

No truncation, finite trace, unproved parent branch, or partial predecessor grammar is used in the mathematical exclusion. The normalizer's termination is proved by the existing original-source theorem. The high stopping equation alone provides actual stopping *input* candidates, without making them reachable.

## Proof lineage and verification boundary

The modular predecessor uniqueness is a direct application of [EvenChild.lean](./EvenChild.lean), `even_child_parent_iff`, valid for odd first/even right≥4, total sum `3 mod8`. Its unique parent has odd right≥5 and total sum `2 mod4`, contradicting [Agent3CImage.lean](../agent3-c-odd-image/Agent3CImage.lean), `section_odd_image`. The stopping equation is from [SectionParam.lean](../agent15-c-halting/SectionParam.lean), and the forced affine orbit equivalence and depth/mass identities from [AffineNormalize.lean](../agent15-c-halting/AffineNormalize.lean) and [AffineParityDepth.lean](../agent15-c-halting/AffineParityDepth.lean).

The prerequisite `seven_four_*` and the one-parameter `high_tower_*` theorems have successfully compiled against the **unchanged** repository Machine C source in [manual CI 41887257726](https://github.com/FlareZ123/bb6/actions/runs/41887257726), with axiom audits exactly standard `propext`, `Classical.choice`, `Quot.sound`. The two-parameter file was independently checked locally with theorem-shaped imported interfaces, but requires successful source-integrated CI before being labeled source-verified. The full-source manual check is dispatched as an isolated `seven_only` path in [the existing workflow](../../.github/workflows/agent3-c-bounce-inverse.yml). Earlier generic default workflow [41884343320](https://github.com/FlareZ123/bb6/actions/runs/41884343320) successfully checked the cone then encountered unrelated, preexisting errors in Agent29 `BottomBoundary.lean`; the isolated path avoids conflating these errors.

No claim here settles Machine C, any other six-state holdout, or an unconditional BB(6) bound. The separate primitive-machine bridge lives in Agent21's source chain and is not reproved by this theorem.

## Reproducible finite quotient contrast

For each input `(a,k)` above, `(a,k,0)` is a genuine hypothetical stopping configuration of the original three-counter C accelerator. Using its exact published `nextC` transition with a representative-expanded **numerical abstract graph**, the following comparisons were independently reproduced:

- The established B8/M32 quotient reaches 31,570 abstract vertices and examines 189,834 edges. For `q=0,n=0`, stopping input `(55,430,0)` projects to an *admitted* vertex `(23,14,0)`.
- The mixed M96 quotient reaches 260,672 and processes 2,022,544 transitions; it also admits tested tower stopping inputs.
- The M256 quotient reaches 3,810,502 and examines 30,131,488 edges. The `q=0,n=1` input `(919,6910,0)` projects to `(151,254,0)` and is **admitted**; the `q=0,n=0` input `(55,430,0)` projects to `(55,174,0)` and is absent. Every `q=0,n≥1` member projects to `(151,254,0)` in this quotient.
- The M512 quotient reaches 27,858,704 and examines 221,572,376 edges. In this quotient the tower `q=0,n=1` target `(919,6910,0)` projects to `(407,254,0)` and is **admitted**; all `q=0,n≥2` project to `(407,510,0)`, also **admitted**. Thus this exact source inverse method can exclude true-blank states that direct abstract target absence in the M512 representative graph does not exclude.

The numeric graph census is an experiment; no complete M512 abstract closure certificate in Lean is claimed. Abstract admission never implies concrete blank reachability. The reusable source [QuotientResolution.cpp](./QuotientResolution.cpp) now reproduces vertex counts and tower projections; invoke it with compatible modulus `M=96,256,512`. Reproduction must verify the original source bridge separately for machine-level claims.

## Distinction from earlier work

Agent29's [sharp forced-depth phase diagram](../agent29-forced-depth/README.md) establishes bounded depth in several weighted-mass sectors and unbounded synthetic affine chains. Its `SecondOneInfinite.lean` proposes an actual stopping family whose normalized right counter is **4** (the special boundary), while the present authentic tower has a variable normalized right `120q+52≥52`, proves exact affine inverse depth `4n+3`, and excludes a separate infinite family using a **two-return ancestry impossibility**. Agent3's earlier fixed three-step and five-step stopping families [HighM1Tower.lean](./HighM1Tower.lean), [HighM1Tower5.lean](./HighM1Tower5.lean) are subsumed by the general tower but remain independent Lean source audit examples. Internal overlap with all existing M512 or deeper quotient results and external novelty still require review.

## Next consequential work

Target the rest of the m=1 high stopping parameter corridor, especially normalized inputs with right≥8 that have multiple source predecessors. Try generalizing the exact inverse cone beyond the y≡4mod8 fixed residue, or derive an all-time forward source invariant covering the remaining stopping family rather than enumerating more modular subfamilies. An exact all-halt-gateway or whole-machine proof is still missing.
