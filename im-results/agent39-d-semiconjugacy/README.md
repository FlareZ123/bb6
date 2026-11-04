# Agent 39: D-family symbolic coalescence, dyadic/ternary shadowing, and aperiodicity

**2026-11-03 | Research pilot [R-20261103T1013Z-agent39-d-semiconjugacy](../../research/issues/R-20261103T1013Z-agent39-d-semiconjugacy.md) | Intermediate.** This dossier contains locally kernel-checked *abstract or explicitly conditional* Lean proofs and independently replayed primitive-machine tests. It does **not** establish an original-source-imported theorem newly checked by CI, a merger of any two genuine blank-root trajectories, a holdout decision, or a new BB(6) bound. External novelty is unassessed.

## Machine, authentic roots, and certified prerequisites

Common original six-state table `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. Write `I_n(y)` for original F scanning 0 with blank tape left and right tape `1^n y 0^infinity`, with physical blank padding, so `I_n(1^j y)=I_(n+j)(y)`. The four *distinct* blank roots of this unrooted family have **individually source-checked** finite initial F sections in shared D0 coordinates:

| Root | F-section unary `n` | Primitive blank offset |
|---|---:|---:|
| D0-A | 9 | 36 |
| D3-B | 5 | 15 |
| D2-C | 15 | 92 |
| D1-F | 39 | 403 |

See [Agent3 rooted conjugacy](../agent3-portfolio-raw-conjugacy/) and [Agent36 four-root projected grammar](../agent36-cryptid-trace/README.md). Different root letters matter: they cannot be conflated by table isomorphism.

Previously formally certified original-machine, arbitrary-suffix return macros:
1. Agent31 `CryptidBoundary.full_B`: `I_(3k+2)(0z) → I_(8k+9)(z)` in `T_B=12k²+49k+40` primitive steps.
2. Agent35 `full_A_code`: for any Boolean word `w`, substitute `Code(false)=10`, `Code(true)=111`, weight `d(w)=#false+4#true`, and primitive packet cost `C(m,w)`, with each `false` increasing `m` by 1 at cost 2 and each `true` increasing `m` by 4 at cost `6m+41`. Then `I_(3k+3)(0 Code(w) 0y) → I_(8k+11+2d(w))(y)` at
   `T_A=12k²+41k+32+C(4k+3,w)+2(4k+3+d(w))+6`.
3. The original machine is deterministic, its `run` composes by time addition, and `I_n(1^j y)=I_(n+j)(y)` holds by literal tape concatenation. Existing certified macro sources and verification are documented at [Agent31's README](../agent31-cryptid-boundary/README.md) and [Agent35's README](../agent35-cryptid-code/README.md), including successful original-source [CI 41416693685](https://github.com/FlareZ123/bb6/actions/runs/41416693685).

The following coalescence is a deduction from these previously verified premises. **Our standalone Lean module imports `Std` and treats those three original-source facts as explicit hypotheses; it does not import and reverify the original six-state modules.** The repository's 2026-11-03 Actions incident currently discourages redundant dispatches of failing manual workflows.

## An all-word, two-arm exact coalescence

**Derived theorem (all `k≥0`, all finite Boolean packet words `w`, all finite tails `y`):**

```text
B-arm: I_(3k+2)(0 1^(2d(w)+2) y)
    --[12k²+49k+40]--> I_(8k+11+2d(w))(y)

A-arm: I_(3k+3)(0 Code(w) 0 y)
    --[12k²+49k+44+C(4k+3,w)+2d(w)]--> I_(8k+11+2d(w))(y)
```

The raw machine reaches **the same physical F configuration** from these two different synthetic tapes. Consequently their future raw orbits agree after the respective prefix times with the constant positive gap
```text
T_A - T_B = 4 + C(4k+3,w) + 2d(w).
```

**Proof:** Apply `full_B` to the B arm, obtaining `I_(8k+9)(1^(2d+2)y)`; absorb the leading ones in the physical tape to obtain `I_(8k+11+2d)(y)`. Apply `full_A_code` to the other arm, which gives the same configuration. Their time difference simplifies to the displayed expression; determinism and the run-addition law propagate equality for every subsequent time. There is no earlier terminal halt, since a permanently halted configuration cannot later produce the certified F-on-0 endpoint.

For `w=[]`, this gives the four-step collision `I_(3k+2)(011y) → I_(8k+11)(y)` versus `I_(3k+3)(00y) → I_(8k+11)(y)`, at `T_B` and `T_B+4`. At `k=0,y=[]` the concrete inputs are `I_2(011)` and `I_3(00)`, meeting at `I_11` after 40 and 44 primitive transitions.

**Lean evidence:** [`Agent39DCodeFunnel.lean`](Agent39DCodeFunnel.lean) gives the all-word theorem `coded_funnel`, exact gap `coded_time_gap`, and arbitrary future equality `coded_funnel_future`. [`Agent39DFunnel.lean`](Agent39DFunnel.lean) proves the empty-word specialization. Both compile locally under Lean **4.36.0-rc2**, with only standard `propext`/`Quot.sound` (some composed abstract consequences have no axioms). All source-specific macro obligations are visible in the `SourceMacroPremises`/`FunnelHypotheses` hypotheses. No `sorry`, `admit`, `native_decide`, or new axioms.

**Independent raw falsification:** [`DFunnelRaw.cjs`](DFunnelRaw.cjs) directly implements the 12 original rules and checks 217 instances, `k=0..30` and seven tails. [`DFunnelCodedRaw.cjs`](DFunnelCodedRaw.cjs) independently checks **10,200** pairs, all binary words up to length 7 (255 words total), `k=0..7`, and five tails. Both validate exact raw primitive counts, F/0 end state, full infinite-tape contents relative to head, and physical absence of written ones left of head. Maximum primitive count per input in the coded test was 3,124; all assertions passed locally on 2026-11-03. These finite tests supplement the all-parameter deduction; they are not themselves a universal proof.

## A universal 3-to-8 prefix-shadowing theorem and nonperiodicity limitation

In the conditional D-family F-return grammar, each supported branch has form

```text
  (n,s)=(3k+r,s)  ->  (8k+c_r(s),s'_r(s))
                    r ∈ {2,3,4}.
```

The suffix transformation and constant `c_r(s)` depend on the branch and suffix, but **not on k**. This source-shaped property is an assumption of our abstract `AffineStep` model, not a new complete analysis of all possible D0 physical suffixes. Only applicable branches from the documented source macros may be asserted physically valid.

[Agent39DShadow.lean](Agent39DShadow.lean) proves for any such decoder, with every finite path of `j` returns starting from `(n,s)` and ending `(N,S)`, the shifted start `(n+3^j d,s)` has an *actual abstract* `j`-step path ending at `(N+8^j d,S)`, for any `d∈Nat`, with identical intervening branch parameters/suffixes. It proves the exact polynomial shift in primitive time when the branch cost is `12k²+(49+24t)k+constant`, where `t` counts consumed `111` A-code packets.

The converse obstruction is also **kernel proved**: two distinct count values, both undergoing the *same* branch constants and suffixes for arbitrary depths, would give the count difference recurrence `3Δ_(i+1)=8Δ_i`. It forces `3^j∣Δ_0` for every depth `j`; a finite positive `Δ_0` cannot satisfy this for all `j`. Thus **no perpetual exact synchronous suffix-and-branch match between distinct unary counts** is possible. This only excludes one strict class of semiconjugacies; transformations between different suffixes, branches, or time indices remain open.

[Agent39DPeriodic.lean](Agent39DPeriodic.lean) strengthens this to a general no-go for any strictly increasing infinite abstract orbit with an eventually periodic pair `(suffix,n mod 3)`. [Agent39DBounds.lean](Agent39DBounds.lean) discharges strict growth from `n≥5` given the D-source-shaped lower offset bounds `c_2≥9,c_3≥7,c_4≥3`. The one potential decreasing small section `n=4,r=4,c=3` is outside that condition. All modules compile locally with final axiom audits `[propext, Quot.sound]`; none proves that an actual blank-root orbit stays indefinitely inside this incomplete conditional return grammar.

## Bounded four-root check and implications

[`d_affine_scan.cjs`](d_affine_scan.cjs) independently ports Agent36's explicitly **conditional** return grammar with `BigInt`. It projected 5,000 returns for each of the four source-backed blank-entry seeds and, at each return, checked shifted input counts `n+3d` for `d=1,3,13,100` against the exact output count `+8d`, branch/suffix equality, and the derived primitive-time polynomial. All checks passed. It found **zero** equal F sections between any pair of root projections, whether at equal macro index or at different macro indices, up to the same 5,000-return cutoffs. Longest same-index runs with both equal suffix and equal branch ranged from 5 to 9 transitions across the six pairs. That is a finite negative search, not a theorem of global nonmerger. Some exceptionally sparse conditional branches and unparsed suffix forms may fall outside the code.

### Research use and next discriminating step

An actual cross-root reduction would require **two separately source-certified blank trajectories** reaching the B and A arms with the *same* `k,w,y`. Then the all-word funnel would yield an exact, finite-time merger of their full physical configurations and hence a transfer of their eventual halting outcome, including a computable runtime offset. No such authentic pair has been found or claimed.

Prioritize searching for **source-constrained B/A-coded predecessor certificates** on genuine D roots, or proving an invariant that excludes such matches. Avoid massive new finite trajectory sweeps and avoid treating the abstract no-periodicity theorem as a proof of D0 nonhalting. Original-source import of the composed funnel theorem is a useful verification task once GitHub Actions execution resumes; its premises are already individually source checked. Assess relevant 2025 @-d prior art before any `results/` promotion.

## 2026-11-04: first authentic original-source D coded-funnel check

The earlier conditional all-word funnel is now **original-source Lean certified**. [`Agent39DOriginalFunnel.lean`](Agent39DOriginalFunnel.lean) imports the unchanged [Agent35 `ABridgeCode.lean`](../agent35-cryptid-code/ABridgeCode.lean), which itself imports the SHA-256-pinned original [Agent31 `Boundary.lean`](../agent31-cryptid-boundary/README.md) and Agent25's token machine. Its main theorems are:

- `BB6.Agent39Source.original_coded_funnel`: for every `k : Nat` and every binary word `ws`, suffix `ys`, the actual six-state raw `CryptidBoundary.run` from `I_(3k+2)(0 1^(2d+2) ys)` and `I_(3k+3)(0 Code(ws) 0 ys)` reaches **identical complete F/0 configurations** at exact times `T_B=12k²+49k+40` and `T_A=12k²+41k+32+C(4k+3,ws)+2(4k+3+d)+6`.
- `original_coded_funnel_future`: after those respective times, their **entire primitive-machine future orbits coincide** for every additional `j : Nat`.
- `exact_delay`: the A input requires exactly `4+C(4k+3,ws)+2d` additional steps to join the B input, with `d=wordInc(ws)`.

**Independent unmodified-source CI [41889534211](https://github.com/FlareZ123/bb6/actions/runs/41889534211) passed 2026-11-04 18:41 UTC** at repository revision `9a04a4b66dc33104a26069064eb3e05b18d4774d`. [Manual-only workflow](../../.github/workflows/agent39-d-original-funnel.yml) hash-restores Agent31 and Agent25 source files, compiles each dependency, then compiles the new theorem with Lean 4.36.0-rc2. `#print axioms` reports **only `[propext, Quot.sound]`** for all three final theorems. No `sorryAx`, local facade axiom, external solver, or copied transition definition occurs in the final proof.

**Scientific boundary:** The theorem composes existing universal original-source macros and is not claimed externally novel. It removes the *source-authentication gap* documented earlier in this dossier, but no common genuine blank-root input pair is known to reach the two arms with matching `k,ws,ys`. No holdout is decided, and no new BB(6) lower/upper bound follows. Next serious mathematical target remains a seed-sensitive reachability certificate or obstruction for either arm, not repeated synthetic tests.
