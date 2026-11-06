# #746: source-exact two-tier odd-ray inverse pruning (Agent 10, 2026-11-06)

**Research status:** These are mathematically uniform first-reset **blank-root** restrictions in the source-C episode semantics of the unmodified Cryptids #746 model. They do not prove that #746 never halts, do not show that all fatal ray indices are unreachable, and do not determine BB(6). The complete inverse grammar always retains genuinely possible exceptional arms. All results belong in `im-results/` pending independent external novelty review.

## Kernel proof provenance

All files import the repo's existing exact `ResetParent`, `ResetChain`, `root_reset_chain_iff`, and the Agent 7 source-connected six-packet selector. Local Lean 4.36.0-rc2 checks used exact signature stubs while drafting. The stronger provenance is the **manual-only GitHub Actions workflow** [agent10-ray-odd-strip.yml](../../.github/workflows/agent10-ray-odd-strip.yml), which compiles the real unchanged source dependency tree before compiling each new file. Final `#print axioms` on source checks reports ordinary Lean axioms `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`, `native_decide`, or new trusted assumption.

- [Source success 42134596250](https://github.com/FlareZ123/bb6/actions/runs/42134596250): [RayOddForkStrip.lean](RayOddForkStrip.lean), initial all-depth fork strip.
- [Source success 42135044167](https://github.com/FlareZ123/bb6/actions/runs/42135044167): [RayOddForkExtended.lean](RayOddForkExtended.lean), narrow-gap 3-adic gate even at residue 2.
- [Source success 42136190557](https://github.com/FlareZ123/bb6/actions/runs/42136190557): [RayForkStripSelect.lean](RayForkStripSelect.lean), exact iff of genuine rooted odd source parents.
- [Source success 42136655199](https://github.com/FlareZ123/bb6/actions/runs/42136655199): [RayPacketHigh.lean](RayPacketHigh.lean), exact six-packet iff under initial sufficient high margin.
- [Source success 42137003763](https://github.com/FlareZ123/bb6/actions/runs/42137003763): [RayGapTone.lean](RayGapTone.lean), exact t=1 odd root iff in narrow dyadic middle gap.
- [Source success 42138048378](https://github.com/FlareZ123/bb6/actions/runs/42138048378): [RayTwoGateExact.lean](RayTwoGateExact.lean) and [RayThirdGeometry.lean](RayThirdGeometry.lean), [RayThirdGate.lean](RayThirdGate.lean), [RayThirdNoRoot.lean](RayThirdNoRoot.lean) originally proved third-level exclusion.
- [Source success 42138575881](https://github.com/FlareZ123/bb6/actions/runs/42138575881): stronger unconditional [RayThirdNoRoot.lean](RayThirdNoRoot.lean) theorem `offray_fork_dead_both_valuation_one`, with no assumed second-root witness; [RayTwoTierSelector.lean](RayTwoTierSelector.lean) exact source fork iff.
- [Source success 42139045493](https://github.com/FlareZ123/bb6/actions/runs/42139045493): [RayTwoTierPacket.lean](RayTwoTierPacket.lean), [RayTwoTierNoTwo.lean](RayTwoTierNoTwo.lean) excluding all t=2 odd inverse parents, and [RayExceptionalDisjoint.lean](RayExceptionalDisjoint.lean) proving high-valuation first- and second-level odd forks cannot coincide.
- [Latest t=3 CI run 42139387238](https://github.com/FlareZ123/bb6/actions/runs/42139387238): [RayTThreeGap.lean](RayTThreeGap.lean) and [RayTwoTierTThreeSelector.lean](RayTwoTierTThreeSelector.lean) have compiled **locally** with source-signature stubs; source CI remains **pending** at the time of this note. Treat these final two files as source-verified only after CI success.

## Actual quantitative symbolic geometry

Write `P=2^n`, `D_j=2^j(2n+3)-(n-1)` as exact natural ray deficit and `u=4P-D_j`. For any `n>=20` in the surviving `n%6∈{4,5}` sectors, any ray depth `j` satisfying the explicit **sufficient** strong margin

```text
2048*D_j + 16384*n + 16384 <= P
```

the source first-reset inverse grammar has especially restrictive genuine root branches. It is a proper subset of the physically admissible region, and the proof makes no inference about deeper ray nodes failing this inequality.

**t=1 odd inverse from ray.** The source odd-band scale is uniquely `k=n-2`. Its reset height `h` and mandatory even parent `w` satisfy

```text
9*h + 8*D_j + 9*n + 7 = 14*P,
2*h = 2*P + w + (n-2),
P < w, 8*w+32 < 9*P.
```

The h→w edge is exact under `27∤(2h+5)`. A rooted w with `27∤(2w+5)` would have an exact t=1 odd predecessor `g` on scale `n-4`. Pure arithmetic forces g and its next three even predecessors into the same scale, and the fourth one into a dyadic image gap. The resulting source-root theorem

```lean
offray_fork_dead_both_valuation_one
```

proves `¬ReachC (2,0) (h,0)` without assuming an externally supplied g. Thus a rooted first t=1 odd branch is possible only if **either**

```text
27 | (2*h+5)  OR  27 | (2*w+5).
```

These exceptions are **mutually exclusive**, as proved for all the surviving index sectors by `not_both_exceptional`. Every rooted source witness remains explicitly quantified in `exact_odd_fork_two_tier_gate`; the proof has no omitted odd scales or postulated finite-branch truncation.

**t=2 odd inverse.** This branch is impossible entirely: any putative `2u+5=27d` places its odd dyadic image quantity `4d` in `(P,3P/2)`, which is outside all odd image bands. The uniform `ray_no_ttwo` is a source arithmetic theorem.

**t=3 odd inverse.** The scale is uniquely `k=n-3`. Its genuine reset predecessor `q` obeys

```text
81*q + 32*D_j + 81*n + 82 = 47*P,
P/2 < q < 3P/4 (strict dyadic image gap).
```

When `q%3 != 2`, all even and odd blank-origin first-parent mechanisms are excluded by the existing root-nonimage theorem. The only source-root possibilities at t=3 have `q%3=2`. The complete iff `exact_odd_root_tthree_residue` retains t>=4 and both t=1 high-valuation gates, with no false conclusion about them.

## Optional exact synthetic-candidate census

[ray_two_tier_scan.py](ray_two_tier_scan.py) computes exact source-algebraic candidates for n20..1500, nmod6 in {4,5}, only in the **strong margin**. Its output (not a formal density or rooted-visit count):

- t=1: **60,950** possible (n,j) source odd-parent candidates. **56,434** satisfy one of the **proved universal** root-exclusion theorems. The **4,516** uneliminated candidates split into **2,259** first-level and **2,257** second-level 27-divisibility gates, disjoint.
- t=3: **6,770** possible (n,j) source odd-parent candidates; **4,514** have precursor residue 0 or 1 modulo 3 and satisfy the gap exclusion, while **2,256** remain at residue 2.
- SHA256 of ordered emitted candidate rows: `a76e297d0807f134227ffb6c725315960ed74911ecf109cfd8c2f20bf7eee363`.

The counts are merely illustrative finite evidence for where the *proven uniform theorems* apply. They do not prove any asymptotic fraction, nonhalting, or BB(6).

## Source-exact frontier

The strongest gate is now: along a high-margin six-packet the genuine blank-root question is exactly a canonical continuation OR an odd-rooted t=1 high 27-valuation at either (but never both) adjacent parent levels OR t=3 with parent residue 2 OR t>=4. A root-sensitive exclusion of these remaining high 3-adic cases, plus control of deeper near-exit ray positions, is necessary before machine #746 can be declared nonhalting. Even that would not solve global BB(6), which requires resolving the full six-state class and a matching universal upper bound. No such claim is made.

Communication: [Agent7 initial note](../../communications/agent7/20261105T2357Z_agent10-general-odd-ray-strip.md) and [second note](../../communications/agent7/20261106T0017Z_agent10-source-deep-fork-pruning.md). New t=3/six-packet results warrant a concise updated note to Agent7 after the final source CI succeeds.
