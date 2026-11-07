# #746 weak-margin no-seam and t=3 genuine-root fork gates

**Agent 10, 2026-11-07. Status: intermediate source-C mathematical research.** The universal weak-margin theorem is verified against the unmodified repository's original source-C reset model in [CI 42330279653](https://github.com/FlareZ123/bb6/actions/runs/42330279653). The complete t=3 low-root, two-gate, double-selector, packet, high-geometry, and high-root import chain now compiles against the actual repository dependencies in [CI 42392225346](https://github.com/FlareZ123/bb6/actions/runs/42392225346) (success). This verifies source elaboration of the selector/packet chain; it does not close the remaining high-q root cases or establish #746 nonhalting. Neither statement settles #746 global nonhalting or BB(6). 

## Independent uniform proof of the Agent 7 weak-margin inverse exit

The uniform arithmetic proof is [RayNoSeam.lean](RayNoSeam.lean); the source recurrence and actual blank-root bridge are [RayNoSeamWalk.lean](RayNoSeamWalk.lean), [RayNoSeamResidue.lean](RayNoSeamResidue.lean), [RayNoSeamRoot.lean](RayNoSeamRoot.lean). They were checked with the real original-source reset definitions in source CI 42330279653, with ordinary Lean axioms only.

Let `n>=20`, `p=2^(n-4)`, and `X=2^j(2n+3)`. The original source two-tier inverse equations produce `B=8p-q` with

    81B+3=16p+128X+169n,
    32X+32n+160<=16p,
    3<=B<=2p+1.

At fixed even-inverse scale `n-4`, the complementary deficit satisfies `C_r=2^r B+(2^r-1)(n-4)`. The theorem `weak_margin_no_seam` proves, for all natural `n,j` satisfying these equations, that `C_r` first enters the strict forbidden interval `(2p+1,4p+3)` at `r=2,3, or 4`. Every earlier `C_i` lies in `[3,2p+1]`, so the exact source inverse `evenWalk` has every intermediate target inside its genuine even-return image band and the final target in the universal no-even-image gap. The key no-skip fact rules out possible windows

    49*2^(n-12)=2^j*(2n+3)+e,
    17*2^(n-13)=2^j*(2n+3)+e,

for `1<=e<=2n`. If `j<=m`, `2^j` divides `e`, forcing a contradictory quadratic bound on the fixed power. If `j>m`, the odd multiplier `2n+3` is already larger than the power coefficient. This is quantified Lean arithmetic without any finite cutoff in the ray index or depth.

Under surviving `n%6 in {4,5}`, a second-generation odd factor with `(2w+5)%27 !=0` forces `SafeResidue (n-4) q`. Combining with Agent 7's genuine-root even-walk theorem, `weak_margin_source_t1_gap_dead` proves `not ReachC (2,0) (h,0)` under the exact source t=1 predecessor equations and both low-valuation gates. This is an **independent derivation overlapping prior work**: Agent 7's [EvenWalkForkDead.lean](../agent7-fatal-density/EvenWalkForkDead.lean) already source-certified the same root exclusion for all `n>=13`, including the small-index residue certificate, in [CI 42329441491](https://github.com/FlareZ123/bb6/actions/runs/42329441491). The independent proof has a smaller purely symbolic growth threshold `n>=20` instead of their `n>=25`, but their complete all-`n>=13` conclusion remains stronger overall. Do not count this as a separately solved holdout.

## New t=3 sector: two levels of exact odd-valuation gates

[RayTThreeLowGeometry.lean](RayTThreeLowGeometry.lean) and [RayTThreeExtendedGeometry.lean](RayTThreeExtendedGeometry.lean) prove the following uniform geometry for any physical t=3 odd inverse `q` from a high-margin canonical source ray, using `P=2^n`, `p=P/16`, deficit `D`, and source's exact relation:

    81q+32D+81n+82=47P,
    2048D+16384n+16384<=P.

It implies the simultaneous strict small-strip constraints

    9p+5n+40<=q,
    q+5n+40<=10p,
    8q+40n+320<=75p.

The target `q` lies in the even-image gap `(P/2,3P/4)`. If its odd numerator is indivisible by 9, then the complete true source first-parent grammar leaves only the t=0 odd arm. Its unique `n-4`-scale parent `h`, satisfying `3d0=2q+5` and `2d0=8p+h+(n-4)+5`, lies in the forbidden gap `(P/4,3P/8)` and has `h%3!=2`; its root exclusion then excludes `q`. The source consequence is [RayTThreeLowRoot.lean](RayTThreeLowRoot.lean); it is included in the successful full-source compile [CI 42392225346](https://github.com/FlareZ123/bb6/actions/runs/42392225346).

For the larger **two-gate** version [RayTThreeTwoGate.lean](RayTThreeTwoGate.lean), exact geometry excludes both t=1 and t=2 odd-parent bands of `q` unconditionally. Thus the remaining odd source inverse arms are t=0 or t>=3. The latter requires `81 | (2q+5)`. The t=0 predecessor `h` lies in a *narrower* gap `P/4<h<(9P/32)-4`, strong enough for the universal source theorem `narrow_gap_root_excluded` if `9` does not divide `2h+5`. Therefore the proposed source-root theorem is

    if 81 does not divide 2q+5
    and 9 does not divide 2h+5
    then not ReachC (2,0) (q,0).

Every higher-valuation arm and both exceptional modular gates are explicitly retained. The complete selector and packet proofs are now compiled against the actual unchanged source dependency chain in [CI 42392225346](https://github.com/FlareZ123/bb6/actions/runs/42392225346). The additional [RayTThreeHighRoot.lean](RayTThreeHighRoot.lean) theorem source-compiles and excludes the high-q subcase when its second parent r has r%3=0. It does not exclude the remaining r%3=1 or r%3=2 cases.

## Reproducible finite illustration, not proof of density or reachability

[tthree_branch_census.py](tthree_branch_census.py) enumerates exact source-algebraic t=3 physical candidates over `20<=n<=1500`, `n%6 in {4,5}`, and the sufficient high margin. The output is:

| Class | Number of algebraic candidates |
|---|---:|
| All t=3 physical candidates | 6,770 |
| Parent q has residue 0 or 1 mod 3, pre-existing gap exclusion | 4,514 |
| q has exact first 3-adic valuation one, new low-q gate | 1,504 |
| q valuation higher, but its unique t=0 parent h has low valuation, two-gate exclusion | 464 |
| Remaining after all gates | 288 |

Of the 288 retained candidates, 84 have `81 | (2q+5)`, and 231 have `9 | (2h+5)`; these two retained classes overlap in 27 cases. These are **finite exact symbolic source-candidate counts**, independent of any assertion that a branch was actually blank-reached. The SHA256 of all ordered candidate rows `n:depth:q\\n` is `3c733a5cfc40389292a056198f1a8716109d132b13485b4fc98e36afe08c309e`.

## Frontier

This research rules out broad uniform families of genuine inverse ancestors but does not prove that the canonical ray never reaches a fatal reset. Higher 3-adic valuation at either t=1 or t=3, the high-index near-exit region outside the strong margin, and all other six-state contenders remain unresolved. The most useful next target is a source-root analysis of the **288 retained** finite illustrative t=3 candidates and their infinite parameter analogues, especially the `81` gate and secondary `9` gate. Retain the exact source inverse grammar and preserve any truly rooted exceptional arms.


## 2026-11-07 16:43 UTC: translated high-q gate and full-source selector compile

The manual source workflow .github/workflows/agent10-ray-odd-strip.yml completed successfully in [CI 42392225346](https://github.com/FlareZ123/bb6/actions/runs/42392225346) at commit bad5cc9fa89bc77e08ad56ceed80f33539651046. It compiled the actual dependency chain through RayTThreeLowRoot, RayTThreeTwoGate, RayTThreeDoubleSelector, RayTThreePacket, RayTThreeHighGeometry, and RayTThreeHighRoot. The source run validates the exact source-C selector and packet equivalences. It does not imply the high-q branch is globally dead.

New intermediate synthesis [TThreeHighGateResidue.md](TThreeHighGateResidue.md) proves on paper that the high-q selector gate 81 | (2q+5) is equivalent to the shifted congruence Z_j(n) ≡ 81*c_n (mod 3^8), with c_n = 38*(2^(n+1)+2n-1) mod 81. Since 2 has order 4374 modulo 6561 and the right-hand side is a unit in sectors n mod 6 = 4,5, the gate selects exactly one j residue modulo 4374. This is a translated Hensel target, not Agent 7's zero-divisibility residue.

The reproducible exact-integer audit [t3_high_gate_audit.py](t3_high_gate_audit.py) finds 3,801 high-q candidates through n=10,000; all their complete reverse cones under the two exact ResetParent arms omit root 2. Maximum cone size is 57, maximum path depth 25. This is finite computational evidence only. No universal root-exclusion theorem has been proved for the remaining r mod 3 = 1,2 branches. The separate secondary t=0-parent gate remains open.
