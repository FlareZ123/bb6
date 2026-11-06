# Historical full research log

**Unabridged snapshot of the former research README, 6 November 2026.** The original mathematical equations, source links, experiments, failed approaches, uncertainty, and chronological proof reports are preserved. Any “pending” or “current” claims below describe the old writing time. For current synthesis use the [maintained README](README.md).

---

# Machine C: exact affine-depth barriers for blank-origin stopping gates

Agent 11, 2026-11-02. **Intermediate mathematical research, original-source CI pending for the newest theorems.** This work does not settle Machine C's halting status, BB(6), or the universal upper-bound task. Preserve in `im-results/` pending reproducible full-chain verification and independent novelty review.

## Principal result: unbounded-depth 2-adic predecessor obstruction

The unmodified original Machine C first-return section map is `BB6.Agent46.secNext`, with blank-origin initial pair `(5,1)`. Write `CReach(a,k)` for exact eventual reachability of pair `(a,k)`, and `oddDepth(k)` for the number of forced affine predecessors when the first counter is 3 mod 4, as in Agent15's source-certified `AffineParityDepth.lean`.

**Theorem (source-composition candidate, `AffineDepthM8.lean`):** for arbitrary naturals a,k satisfying
```text
a%4 = 3,
(a+2*k)%8 = 7,
oddDepth(k)%2 = 0,
k+2 = 2^oddDepth(k) * (8*q+6)   for some q,
```
we have `¬CReach(a,k)`. This is a whole two-dimensional, variable-depth reachable-set obstruction, quantified over unbounded counters and depths. Proof: let `(A,K)=affineNormalize(a,k)`, the **exact** blank-reachability-preserving forced inverse from Agent15's `ReachAffine.lean` and `AffineNormalize.lean`. Its formally derived invariants are `A+2K+4*oddDepth(k)=a+2k` and `2^oddDepth(k)*(K+2)=k+2`. The assumptions imply `(A%8,K%8)=(7,4)`, contradicting the source-certified full-orbit quotient theorem `blank_no_m8_cylinder`. The proof is independent of simulated blank trajectories or any fixed recursion-depth search limit.

**Consequence (`DeepLowGate.lean`):** for every odd positive u, if `d=oddDepth(21u−3)` is even and `21u−1=2^d(8q+6)` for some q, then `¬CReach(1,32u+4)`. Agent3's exact three-section `low_gate_all_parents_iff` forces every such low gate to derive from the state `(22u−3,21u−3)` because the odd u excludes every higher even-bounce inverse depth. Its first counter is 3 mod4, weighted sum 7 mod8, and the general invariant above eliminates it.

**Unbounded hierarchy (`DeepFamily.lean`):** the source expression `oddDepth` has the universally quantified exact formula
```text
oddDepth(2^(2r+1)*(4q+3)−2) = 2r
```
for every r,q. Therefore for any r,q,u with
```text
21u−1 = 2^(2r+1)*(4q+3)
```
the genuine blank section never reaches `(1,32u+4)`. Its proof is a complete induction over r and two exact inverse steps at each induction successor. There is no bound on r. For each fixed r the Diophantine condition has infinitely many positive solutions: choose q satisfying `2^(2r+1)*(4q+3)≡−1 (mod21)` and increase q by 21. Since 21 is odd and coprime to 2, and multiplication by 4 is invertible modulo21, the condition has exactly one class of q modulo21. It determines a whole infinite nonreachability family at arbitrary forced-inverse depths.

## Explicit machine-halting parameters removed

The original Agent15 first halting family has the exact equation `k+3m+4=2^(2m+3)` and requires reaching `(1,k)`. Repeated use of Agent3's complete inverse and the above quotient/normalizer forbids the following entire index congruences:

| First-halt index | First-family candidate gate | Source theorem | Status |
|---|---|---|---|
| `m%256=136` | `k%256=100`, `t=(k−4)/16%16=6` | `LowGate6.first_halt_m136_mod256_unreachable` | Lean source job 41519952402 pending |
| `m%1024=456` | `k%1024=676`, `t%64=42` | `AffineDepthM8.first_halt_m456_mod1024_unreachable` | Lean source job 41522387396 pending |

These two classes are **disjoint**: the former is `m%256=136`, the latter `m%256=200`, and both lie in `m%16=8`, a sector that passed Agent15's earlier `affineQuotientExcluded` filter. Passing that filter never implied reachability. The general Diophantine hierarchy subsumes these as r=0 and r=1. It yields additional all-time low-gate exclusions for arbitrarily large r, without requiring a finite residue-class enumeration.

## Formalization files and provenance

- [`AffineDepthM8.lean`](./AffineDepthM8.lean): all-natural affine normalization exclusion; explicit two-level residue witness; `t%64=42` and first-family `m%1024=456`.
- [`DeepLowGate.lean`](./DeepLowGate.lean): uniform all-depth odd-u gate obstruction.
- [`DeepFamily.lean`](./DeepFamily.lean): exact unbounded `oddDepth` induction and Diophantine hierarchy.
- [`LowGate6.lean`](./LowGate6.lean): t%16=6 and first-family m%256=136.
- Original source dependencies: Agent3 [`EvenTargetOrbit.lean`](../agent3-c-bounce-inverse/EvenTargetOrbit.lean), source CI [41513332787](https://github.com/FlareZ123/bb6/actions/runs/41513332787); Agent15 [`AffineParityDepth.lean`](../agent15-c-halting/AffineParityDepth.lean) and [`M8M16Composition.lean`](../agent15-c-halting/M8M16Composition.lean); Agent41/43 quotient [`Mod8SevenFour.lean`](../agent41-c-quotient512/Mod8SevenFour.lean) with original CLine source.
- Two manual **original-source** CI invocations: [41519952402](https://github.com/FlareZ123/bb6/actions/runs/41519952402) (first low-gate), [41522387396](https://github.com/FlareZ123/bb6/actions/runs/41522387396) (full all-depth hierarchy). The same existing `.github/workflows/agent15-c-halting.yml` compiles original imported source and prints every new theorem's axiom set. These jobs were still in progress at the time of this update. In the local environment Lean 4.36.0-rc2 accepted all exact proof bodies against matching theorem signatures, with no sorry. That preliminary check is **not** a substitute for full-source compilation.

## Earlier independent verification, explicitly credited as prior art

[`First24.lean`](./First24.lean) shows all first-family `m%32=24` unreachable by combining Agent15's exact single-affine predecessor with Agent38's blank `odd_special` exclusion. Complete original-source Lean CI [41518668629](https://github.com/FlareZ123/bb6/actions/runs/41518668629) passed, axioms exactly `[propext, Classical.choice, Quot.sound]`. **Agent3 had already proved a stronger theorem `low_gate_odd_t_excluded`** encompassing this residue. Consequently `First24` is an independent sanity check only and carries **no claim of mathematical novelty**.

## Open problem

The above barriers are one-sided exclusions. The remaining uncountable-in-computation infinite families of halting input parameters are not all eliminated, and Machine C remains undecided. A stronger global forward invariant or an infinite inverse argument covering the residual halting family would still be necessary for a whole-machine nonhalting theorem. The overall exact BB(6) objective further requires resolving all other holdout machines and a complete universal proof of the six-state enumeration bound.

## 22:30 UTC continuation: uniform first-halt index hierarchy and verification repair

A new all-natural Lean source candidate [`FirstUniform.lean`](./FirstUniform.lean) upgrades the individually enumerated first-family exclusions to the following **single parameterized theorem**, for arbitrary `m,k,r,s,t : Nat`:

```text
m = 64*s+8
63*s+11 = 2^(2*r)*(4*t+1)
r+3 <= m
k+3*m+4 = 2^(2*m+3)
----------------------------
NOT CReach(1,k)
```

The exact arithmetic lift is `k = 32*u+4` and `21*u-1 = 2^(2*r+1)*(4*q+3)` for some naturals u,q. This reduces the stopping parameter to `DeepFamily.deep_low_gate_diophantine`, the older exact unbounded-depth inverse-reachability obstruction. Because 63 is coprime to every power of 4, the index condition has a solution s modulo `4^(r+1)` for each fixed r; adding multiples of `4^(r+1)` yields infinitely many indices. This is an algebraic observation, separate from the Lean source theorem. For r=0,1,2 the smallest positive index classes are respectively m≡136(mod256), m≡456(mod1024), and m≡3784(mod4096). The third class has a dedicated exact [`FirstR2.lean`](./FirstR2.lean) instance. These three classes are disjoint.

**Evidence status:** the proof body of `FirstUniform.lean` was accepted by Lean 4.36.0-rc2 in a local test **with an explicitly assumed upstream `deep_low_gate_diophantine` statement**. The two new files are committed, and the *full original-source compilation* is being dispatched through the existing manual `agent15-c-halting.yml` workflow. This local isolated typecheck is **not a complete kernel verification of the source-integrated mathematical claim**. The final axiom audit and any failed CI logs take precedence over this preliminary status.

Two preceding manual original-source CI attempts [41519952402](https://github.com/FlareZ123/bb6/actions/runs/41519952402), [41522387396](https://github.com/FlareZ123/bb6/actions/runs/41522387396) failed **before reaching these Agent11 theorems** because `AffineQuotientExclusion.lean` used `affineExcluded` without importing `AffineExclusion`. This concrete dependency defect has now been corrected, and the workflow is also updated to emit the imported `.olean` files for `DeepLowGate` and `DeepFamily`. The repaired source chain must pass CI before changing these entries to certified mathematical results. The underlying Machine C nonhalting problem and BB(6) remain open.

### Exact nonvacuity at every inverse depth (22:42 UTC)

Three further small Lean modules make the index hierarchy mathematically explicit:

- [`IndexWitness.lean`](./IndexWitness.lean) **compiled locally without assumed arithmetic axioms** (axioms `[propext, Quot.sound]`): for every natural depth r, some s,t solve `63s+11=4^r(4t+1)`; for every lower bound L, there are such solutions with `s≥L`. The completely explicit recurrence is `(r,s,t)→(r+3,64s+11,t)`, starting from `(0,2,34)`, `(1,7,28)`, `(2,59,58)`. For fixed r, a further lift is `(s,t)→(s+4^(r+1)N,t+63N)`.
- [`IndexDisjoint.lean`](./IndexDisjoint.lean) **compiled locally with standard axioms only**: the exact depth r is unique for any fixed s, hence these infinitely many per-depth families are pairwise disjoint.
- [`IndexLift.lean`](./IndexLift.lean) and [`IndexReach.lean`](./IndexReach.lean) lift the unbounded witnesses through `FirstUniform` and show the stopping candidates are genuine positive-integer solutions of the first-family Diophantine equation. Specifically, for every r,L, there exist `m≥L,k` with `k+3m+4=2^(2m+3)` and `¬ CReach(1,k)`. **These two source-linked conclusions were tested locally using an explicitly assumed DeepFamily theorem signature and still require original-source CI**, with no stronger claim made.

The index condition selects precisely one s-residue modulo `4^(r+1)` for each r (since 63 is invertible modulo powers of four), giving a formalizable geometric family of disjoint congruence exclusions. Elementary density reasoning yields a natural density of 1/3 among the first-family indices with `m≡8(mod64)`, or 1/192 among all nonnegative m, after taking the union over every depth r; this *density statement is presently mathematical analysis, not an additional Lean-audited theorem*. It does not measure how close Machine C is to a complete halting decision.

### Search-direction falsifiers and a conditional higher-modulus bridge (22:53 UTC)

A direct implementation of the original `FastSectionDef.lean` section map, run for 200,000 returns from the genuine start `(5,1)`, found **actual visits** to all three complement classes of the simple M8 residue barrier:
`(3,4)` at return 1, `(75,16)≡(3,0)(mod8)` at return 16, and `(31,104)≡(7,0)(mod8)` at return 37. The finite trajectories were independently checked by local Lean 4.36.0-rc2 using an exact copied original `bounce`, `exactSection`, and run, with standard axioms only; [`ResidueWitness.lean`](./ResidueWitness.lean) compiles the same 38-step chain with original imports and awaits CI. This decisively defeats any attempt to exclude each *entire* complementary mod8 cylinder. The 200,000-return experiment is computational evidence only.

An independent B8/M32 abstract finite-quotient BFS reproduced Agent43's known 31,570 reachable vertices, 189,834 edges. It found two absent section cells `(27,28,0)`, `(19,16,0)` that are *present in the M8 and M16 overapproximations*. Those absences are currently experimental and **must not be called source-kernel-certified**. Exact arithmetic points to new first-family index cylinders `m≡584` and `m≡1864` (mod 2048), respectively, disjoint from the existing all-depth M8 families.

[`M32PullbackConditional.lean`](./M32PullbackConditional.lean) is a sorry-free conditional proof. Given precisely the two M32 cylinder nonreachability hypotheses, it excludes both above first-family classes by Agent3's exact low-gate parent grammar and a single forced affine inverse (the terminal pair is `((43u−8),((21u−5)/2))` for odd `u`). This proof body typechecked locally against *explicitly assumed upstream source signatures*. It imports the actual source in the repository and is queued for full-source compilation. An original M32 closure certificate is being developed by Agent43. Agent11 has **not** attempted to duplicate or prematurely assume that certificate. Targeted coordination message: `communications/agent43/2026-11-02T2248Z_agent11-first-family-m32-targets.md`.

This is a potentially stronger research route if the M32 certificate becomes kernel verified. Machine C, BB(6), and the corresponding universal upper bound remain unresolved.

## 23:10 UTC: an unbounded second-family exclusion at every inverse depth

The earlier work concerned primarily Agent15's *first* stopping family. A structurally new Lean theorem now targets the genuine **second** stopping locus
`k+j+3m+5=2^(2m+2)*(j+3)`, whose candidate source section state is `(2j+3,k)`.

[`SecondUniform.lean`](./SecondUniform.lean) derives:
```text
m%4=3,  r+2≤m,  q≤j,
j+3m+3=2^(2r+1)*(4q+1),
k+j+3m+5=2^(2m+2)*(j+3)
--------------------------------------------
¬ CReach (2j+3) k
```
It establishes `(2j+3)%4=3`, weighted counter mass `(2j+3+2k)%8=7`, and exactly even inverse normalization depth `oddDepth k=2r`, by expressing `k+2=2^(2r+1)*(4Q+3)` for a natural `Q≥1`. The final nonreachability invokes Agent11's already-source-connected **`normalize_even_depth_m8_forbidden`**. The proof has passed local Lean 4.36.0-rc2 with an *explicitly assumed exact signature* for that imported theorem; complete original-source compilation is scheduled by `agent15-c-halting.yml` and is NOT YET VERIFIED.

More importantly, [`SecondWitness.lean`](./SecondWitness.lean) proves the family is **nonvacuous at every inverse depth**: for every r and lower bound L, it constructs actual naturals m≥L,j,k satisfying the complete second stopping Diophantine equation and whose candidate section state is blank-unreachable. Its construction is explicit:
```text
m = 4(r+L)+3
P = 2^(2r+1)
q = m
j = P(4m+1) - 3m - 3
k = 2^(2m+2)(j+3) - j - 3m - 5 .
```
Lean proves each subtraction is nonnegative and the required equations hold for all naturals r,L. Local typecheck has standard Lean axioms plus the named imported source theorem signature; no sorry. The witness output also states `r=0 ∨ j%4=0`, using the **independently locally kernel-checked** [`SecondResidue.lean`](./SecondResidue.lean): for r≥1, `j%4=0`. Thus positive-depth families lie outside Agent41's M8 j≡2(mod4) halting-parameter exclusions; their first counter is ≡3(mod8), right counter even. They are not already detected by Agent38's odd-right-counter modular exclusion. This is a mathematical structural extension, NOT a Machine C decision.

Two more general source-targeted modules [`OddDepthGeneric.lean`](./OddDepthGeneric.lean) and [`OddDepthResidue.lean`](./OddDepthResidue.lean) show for arbitrary d and q≥1:
```text
oddDepth(2^(d+1)*(2q+1)-2)=d.
For a%4=3, mass a+2k≡23(mod32), k+2=2^(d+1)*(2q+1):
  normalized B=4q, (A+8q+4d)%32=23.
```
The first theorem was locally kernel-checked with only ordinary axioms and an exact copy of the original `oddDepth` definition. The second has been locally checked against a clearly marked *assumed upstream* `normalize_three_depth_invariants` signature. The full original imports are committed for source CI.

[`M32AllDepthConditional.lean`](./M32AllDepthConditional.lean) adds a **formally conditional** classification of eight B8/M32 absent quotient cells at all inverse depths. Its `hcyl` is an explicit nonreachability hypothesis: the actual M32 graph closure must be fully source-kernel-certified by Agent43 before any unconditional exclusion follows. It does NOT promote computational BFS absences to proven mathematical results.

**Verification pipeline:** the combined original-source workflow has been updated with every module (commit `44363fe624186150f1a3e267ef3b46c74286ae72`). Run [41537821482](https://github.com/FlareZ123/bb6/actions/runs/41537821482) reached 22:56 and failed on a checkout-directory `cp` path bug (missing `$GITHUB_WORKSPACE` prefix), not an identified Lean theorem error. That bug is fixed at commit `332b01562e7e365231778cf1948a6521fd0e601b`. Replacement manual original-source run [41541712198](https://github.com/FlareZ123/bb6/actions/runs/41541712198) was dispatched 22:58:44 UTC and was still compiling at the time of writing. It contains modules committed up to that earlier head; the latest 23:10 additions require another source run. Treat all source-integrated new claims as pending until CI success and standard-axiom audit, while the self-contained arithmetic theorems have already compiled locally.

## 23:24 UTC decisive verification update: original M32 eight-cylinder theorem PASSED

**The underlying Machine C M32 graph certificate has now passed fully.** [Agent43 Actions run 41538277695](https://github.com/FlareZ123/bb6/actions/runs/41538277695), head `640d616ac420281216ad5f197ab255c07982035f`, verifies every one of the 40 blocks (eight successful parallel proof shards), the global closure theorem and an exact original `BB6CLine.nextC` reachability bridge. The final source theorem `CCert.original_low_twenty_unreachable` has only standard Lean axioms `[propext, Classical.choice, Quot.sound]`.

**Agent11's eight-cell extension is now ALSO full original-source kernel verified**. [Fast CI run 41544958543](https://github.com/FlareZ123/bb6/actions/runs/41544958543), success 2026-11-02 23:23:45 UTC, head `a41218e58b30499b9082b61e54b1975479e35963`, recompiled original quotient source and its original CLine bridge using the exact already-kernel-checked 40 block artifacts from successful Agent43 run 41538277695. It then compiled [`M32EightCells.lean`](./M32EightCells.lean), which discharges ALL eight modular emptiness predicates against the actual generated finite `seen` bitset using Lean's kernel `decide`. The log audits `'CCert.original_eight_unreachable' depends on axioms: [propext, Classical.choice, Quot.sound]`. No `sorryAx` or developer assumptions. Proven statement:
```text
∀ x y : Nat,
 (x%32,y%32) ∈
 {(27,28),(19,16),(3,20),(11,0),
  (3,16),(11,12),(19,4),(27,0)}
 → ¬ BB6CLine.Reach (x,y,0)
```
This includes the tricky low- versus high-counter quotient representatives, all checked in Lean. The intermediate first failed CI 41544608759 was a syntactic `base` constant unfolding/maxRecDepth issue; fixed and rerun successfully.

[`M32AllDepthOriginal.lean`](./M32AllDepthOriginal.lean) is the source *composition proof candidate* that applies this newly certified original-CLine theorem to the authentic source section via `BB6.Agent15.m8_section_reach_embeds`, then to arbitrary odd-depth affine inverse classes via `M32AllDepthConditional.m32_odd_depth_reach_barrier`. It also derives unconditional (in its theorem statement) first-family index exclusions `m%2048∈{584,1864}`, using the earlier source `M32PullbackConditional`. **This final combined-import source module has NOT YET passed an original-source CI audit; its exact claims remain provisional pending that compilation**, despite the full verification of the eight upstream CLine cylinders. [`M32NovelResidues.lean`](./M32NovelResidues.lean) is a fully locally Lean-checked independent number-theoretic theorem showing these two new first-family residue classes are disjoint from every original even-depth M8 Diophantine hierarchy class. This means the M32 improvement is mathematically nonredundant against that prior family.

New primary successor task: compile `M32AllDepthOriginal.lean` with both source-authenticated Agent15 section bridge and now source-certified Agent43 M32 quotient imports, reusing the 40 already-verified P32Block artifacts if possible. The 40-block certification is already complete; avoid recomputing it unless provenance requires it. No universal resolution of Machine C or BB(6) has been established.
