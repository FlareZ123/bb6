# Machine C: valuation-six inverse sectors and two infinite stopping obstructions

**Status (6 November 2026): original-source Lean 4.36.0-rc2 verifies both inverse sectors and the two-dimensional blank-root obstructions. The global halting problem for Machine C, the other BB(6) holdouts, and BB(6) itself remain unresolved.** This is an intermediate research record in `im-results/`; external novelty and publication scope must be assessed separately.

## Model and evidence boundary

The original six-state Machine C is `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`. Its actual blank-rooted section starts at `(5,1)` and evolves by the unchanged `BB6.Agent46.secNext` from [FastSectionDef](../../im-results/agent46-c-jump/FastSectionDef.lean). `BB6.Agent3.CReach x y` is existential reachability from that authentic initial pair, with no synthetic start, cutoff, or finite quotient. Existing source-certified facts are the original section's odd-right image invariant, the exact affine original-root reachability equivalence, the odd/odd low-valuation gate, and the even/odd seven gate.

## The first valuation-six sector: a completely empty blank cylinder

[ValSixArithmetic.lean](ValSixArithmetic.lean), [ValSixInverse.lean](ValSixInverse.lean), and [ValSixSource.lean](ValSixSource.lean) establish:

```text
x % 16 = 13
y % 16 = 2
(x + y + 1) % 256 = 64
34 <= y
320 <= x + y + 1
-----------------------------------
not CReach x y
```

For *every* source predecessor `secNext (a,k)=some(x,y)`, the original source exhaustive inverse permits only three candidate branches:

```text
direct:    a = x+y-2,       y = 2*k+2
bounce 1:  4*a+12 = x+y+1,  2*k+a+10 = x+2*y
bounce 3: 16*a+48 = x+y+1, 2*k+a+16 = x+2*y
```

Odd bounce-source parity and valuation force recursive depth 1 or 3. The exceptional `a=1` source would demand `x+y+1=16*2^n`, impossible under the size and modular assumptions. A bounce-1 source has odd right counter >=5 and coordinate sum 2 modulo 4, contrary to the authentic blank-image theorem. Both the bounce-3 and direct sources have even right counters and sum 1 modulo 4, so the exact affine reachability equivalence moves either one to a source with odd right counter >=5 and sum 2 modulo 4. Hence no possible input lies on the genuine blank orbit.

A distinct **infinite high-stopping candidate family** is therefore excluded (Lean files [ValSixHighArithmetic.lean](ValSixHighArithmetic.lean), [ValSixHighSource.lean](ValSixHighSource.lean)):

```text
4 <= m, m % 8 = 4, (j+191)%256 = (3*m)%256,
k+j+3*m+5 = 2^(2*m+2)*(j+3)
-----------------------------------------------
not CReach (2*j+3) k
```

The progression `(j,m)=(77+256*n,4+256*n)` lies in this candidate family for all natural `n`. Its first instance has `j=77,m=4,k=81826`, a *formal stopping-input candidate*, never a claimed genuine halt.

## Complementary valuation-six sector: a true-root inverse iff

[ValSixSecondArithmetic.lean](ValSixSecondArithmetic.lean), [ValSixSecondInverse.lean](ValSixSecondInverse.lean), [ValSixSecondSource.lean](ValSixSecondSource.lean) prove:

```text
x % 16 = 5
y % 16 = 10
(x + y + 1) % 256 = 192
-------------------------------------------------
CReach x y  <->  CReach (x+y-2) ((y-2)/2)
```

The original map genuinely has two additional bounce predecessor branches; their *authentic blank-root* reachability is impossible. One bounce source violates the original odd-image theorem immediately; the other violates it after its exact affine predecessor. The source's exceptional `a=1` branch is impossible without a separate magnitude guard here. Conversely, the displayed direct edge exists in the unchanged original map, proving the backward equivalence in both directions.

A four-link source-authentic consequence is the **entirely empty second two-dimensional blank cylinder** ([ValSixSecondConeArithmetic.lean](ValSixSecondConeArithmetic.lean), [ValSixSecondConeSource.lean](ValSixSecondConeSource.lean)):

```text
x % 256 = 165, y % 256 = 26   ==>   not CReach x y
```

Explicitly write `x=256*p+165, y=256*q+26`. The four root-equivalent backward gates lead from target `(x,y)` to:

```text
1. direct:  (256*(p+q)+189, 128*q+12)
2. affine:  (256*p+384*q+199, 64*q+5)
3. odd/odd: (128*p+224*q+100, 64*p+144*q+51)
4. even/odd: (96*p+184*q+73, 80*p+164*q+61)
```

The terminal counter is odd and >=61, and the terminal coordinate sum is `176*p+348*q+134`, congruent to 2 modulo 4. This contradicts the source-derived blank odd-image invariant for *every time*, with no simulation horizon.

Another infinite true-source high-stopping candidate family follows, proved in [ValSixSecondHighArithmetic.lean](ValSixSecondHighArithmetic.lean) and [ValSixSecondHighSource.lean](ValSixSecondHighSource.lean):

```text
4 <= m, j % 128 = 81, (j+63)%256 = (3*m)%256,
k+j+3*m+5 = 2^(2*m+2)*(j+3)
-----------------------------------------------
not CReach (2*j+3) k
```

The unbounded progression `(j,m)=(81+128*n,48+128*n)` lies in this second disjoint candidate family.

## Relation to prior finite and infinite high sieves

These congruence families are absent from prior Agent3, Agent19, and Agent29 listed high exclusions for examined instances. In both families `(2*j+3)%8=5`, whereas Agent19's unbounded dyadic exclusion requires an 8-residue of 7 or 3; its full exponent quantifier therefore cannot exclude these families. [ValSixNovel.lean](ValSixNovel.lean) contains the stronger universal arithmetic theorem that all two new candidate families satisfy **every** earlier combined `Agent29Joint.highAllowedPlus` condition, with explicit unbounded progressions. Check its latest original-source CI status before treating that universal nonredundancy as certified.

[ValSixJoint.lean](ValSixJoint.lean) extends the prior original-source exact halting iff `Agent29Joint.blank_halts_iff_joint_mod128` by excluding both new high candidate families. This retains the exact Boolean fixed-target root decision for each remaining parameter and deliberately preserves the unresolved **infinite existential** over low and high candidates. Its separate source-check status must be verified.

## Reproducible validation

- **First cylinder and high stopping family:** [original-source CI 42227178958](https://github.com/FlareZ123/bb6/actions/runs/42227178958), success, `#print axioms` on decisive theorem exactly `[propext, Classical.choice, Quot.sound]`.
- **Complementary exact root iff and second empty cylinder:** [original-source CI 42228998913](https://github.com/FlareZ123/bb6/actions/runs/42228998913), success, same three standard axioms.
- The updated manual-only source verification workflow is [agent29-mod128-root.yml](../../.github/workflows/agent29-mod128-root.yml). It builds the original unmodified Machine C source before the new modules.
- The strengthened joint halting iff is under the original-source [agent29-joint-mod128.yml](../../.github/workflows/agent29-joint-mod128.yml); the latest run should be checked independently for conclusive status.
- All source files above contain explicit theorem statements and `#print axioms`. The first three-branch classification is exhaustive, including low-counter source exceptions.

## Scope and next mathematically productive directions

The complement `x%16=5, y%16=10, (x+y+1)%256=192` outside `y%256=26` remains partly unresolved, despite its exact one-parent blank-root reduction. The infinite surviving low and high halting parameter families remain unsolved. Integrating this second source-certified inverse into an exact repeatedly-normalizing root solver may expose additional no-root families. The route to BB(6) still requires resolving all outstanding machines and a global proof of maximality; these Machine C partial obstructions alone do not establish nonhalting.


## New third valuation-six source-root obstruction (source certified 14:14 UTC)

The complementary true-root iff from `ValSixSecondSource.lean` supports a **strictly larger three-link all-time empty blank cylinder**, independent of the earlier four-link `x%256=165,y%256=26` condition:

```text
y % 64 = 58, (x+y+1) % 256 = 192   ==>   not CReach x y.
```

[ValSixThirdConeArithmetic.lean](ValSixThirdConeArithmetic.lean) proves the exact modular preconditions for three original-source inverses. [ValSixThirdConeSource.lean](ValSixThirdConeSource.lean) applies (i) the new source-exact sum-192 root iff, (ii) Agent15 exact affine reachability iff, (iii) Agent3 low-valuation odd/odd unique-root equivalence. The forced terminal counter is odd, at least five, with sum 1 mod4, excluded globally by the authentic blank odd-image invariant. The arithmetic includes the full low boundary; no simulation horizon or unproved parent is assumed.

The resulting **third disjoint infinite high stopping candidate exclusion** is proved by [ValSixThirdHighArithmetic.lean](ValSixThirdHighArithmetic.lean), [ValSixThirdHighSource.lean](ValSixThirdHighSource.lean):

```text
m >= 4, j % 32 = 1, (j+63)%256=(3*m)%256,
k+j+3*m+5=2^(2*m+2)*(j+3)
    ==> not CReach (2*j+3) k
```

The unbounded explicit index progression `(j,m)=(33+256*n,32+256*n)` satisfies these arithmetic restrictions for every natural n. **Original unchanged Machine C source CI [42231672498](https://github.com/FlareZ123/bb6/actions/runs/42231672498) SUCCESS** compiled all four third-cone modules and printed only standard Lean axioms for `third_cone_blank_unreachable` and `high_third_cone_blank_unreachable`.

[ValSixJointThree.lean](ValSixJointThree.lean) strengthens the previous exact source-root halting iff by excluding this third infinite family, retaining every earlier high and low restriction; [ValSixThirdNovel.lean](ValSixThirdNovel.lean) establishes independent universal prior-sieve nonredundancy and explicit unbounded previous admissibility. The strengthened exact halting iff in `ValSixJointThree.lean` passed full unchanged-source [CI 42231902776](https://github.com/FlareZ123/bb6/actions/runs/42231902776), with only `[propext, Classical.choice, Quot.sound]` axioms. `ValSixThirdNovel.lean` is pending original-source CI in a later run.

[ValSixMixedNormalize.lean](ValSixMixedNormalize.lean) is a further proposed reusable integration: it combines all four prior source-exact forced inverse normalization gates with the new second valuation-six forced gate, terminates on weighted rank `x+2*y`, and composes a source-exact fixed-target Boolean blank-reachability oracle with the normalized state. Its novel value is possible additional repeated inverse pruning beyond the current three cylinders. It is **pending original-source CI** and should not be treated as certified until compiled and axiom-audited.

The general Machine C nonhalting question remains open. The strongest immediate program is to exploit the new source-exact normalizer on surviving *unbounded* low/high halting loci, aiming for a semantic invariant that rules out every candidate, rather than accumulating disconnected residue exclusions.
