# Machine C: signed-residue all-parent cone certificates

**Current status.** The proof-only `CompressedMemo` source closure passed original-source CI 45485987157. `KernelCone.lean` adds a structurally reducible all-parent exclusion checker; its generic soundness proof and low-stop m=10 Boolean certificate compiled locally against the verbatim executable arithmetic definitions. The full original-source closure, including `lowStop10_not_reachable`, passed CI 45497710445. The first pure-power high-stop seed above the earlier terminal-mass cutoff is computationally excluded by a 540-fuel tree; its full kernel certificate is not yet accepted. The unbounded Machine C parameter existential remains open; no BB(6) value is claimed.
## Exact classification of exceptional pure-power stopping sums (PurePowerStop.lean)

The usual necessary inverse law excludes rounded sums Q=x+y+(x+y mod 2) that are pure powers of two. This is now a completely classified arithmetic subset of the genuine stopping equations, rather than an unspecified singular case.

For a high target x=2j+3, k+j+3m+5=P(j+3), P=2^b, b=2m+2, write o=(j+m) mod 2. Then Q=(P+1)(j+3)-(3m+5-o). For m>=1, the complement c=3m+5-o lies in [1,P/2]. Powers of two modulo P+1 have the exact residue 2^(v mod b) if floor(v/b) is even, and P+1-2^(v mod b) if it is odd. Thus Q=2^v iff the latter parity holds, c=2^(v mod b), and (P+1)(j+3)=2^v+c. Modulo three determines o from the remaining exponent.

The complete positive-index parametrization is, for every r>=3 and s>=0,

    m=(2^r+1-(r mod 2)-5)/3
    b=2m+2
    v=b*(2s+1)+r
    j=(2^v+2^r)/(2^b+1)-3
    k=2^b*(j+3)-(j+3m+5).

Both directions are proved, including integrality, nonnegative natural subtraction, and the canonical stop equation. The m=0 boundary has Q=2^v iff v>=4, v=0 mod4, 5(j+3)=2^v+4. In the low stopping family, Q is strictly between 2^(2m+2) and 2^(2m+3), for every m>=0, so no pure-power exception occurs there.

All nine printed theorem profiles compiled locally on 4.36.0-rc2 with standard axioms only. The key exact construction is family_exact and its exhaustive converse is high_power_family_complete. This arithmetic classification is independent of the source-parent axioms and makes no claim of actual reachability or nonreachability of any pure-power member. Subsequent proof work should target these explicit exponent families rather than using the non-power parent law on them.

## Unbounded forced prefix followed by a genuine inverse branch (BranchingBlocks.lean)

The earlier Agent42 DirectBlocks theorem is reused, not reproved. Write y+2=2^(t+1)H with H>=7 odd. If (x mod 4,H mod 4) is (3,3) or (0,1), the first t direct inverse edges are forced and lead to (a,2H-2), preserving the left residue modulo four and reducing weighted mass x+2y by 4t. The terminal is genuinely outside the six-residue forced-direct gate. If its rounded sum is 24 modulo 32, its valuation is exactly three and the necessary inverse grammar admits only the direct and depth-one alternatives. Both parents satisfy the forbidden odd-right criterion. The test is equivalently

    (x+2y+28t+2+(x mod 2)) mod 32 = (2H+24) mod 32.

The proof excludes the entire unbounded family without spending one bit of a finite modulus budget per step. The executable branchingBlockExcluded derives t,H from the exact right counter; its accepted set is proved disjoint from Agent42's earlier direct-only certificate. No claim of disjointness from all prior integrated sieves is made.

For high stopping targets x=2j+3, k+j+3m+5=2^(2m+2)(j+3), the sufficient phase condition becomes H+3m+2t+14=0 mod 16, with H=3 mod 4. An explicit infinite two-parameter family is m>=5, m=1 mod 4, q>=1, q=11m+4 mod 32, j+3m+3=q*2^(2m+2). The block has t=2m+2; H=(j+3-q)/2. It exhausts the original signed-cone precision budget before the branching terminal. For m>=17 the prefix also exceeds the current 32-bit cap.

All six exported theorems in BranchingBlocks.lean compiled locally on Lean 4.36.0-rc2 against the verbatim existing DirectBlocks.lean (only propext, Quot.sound, and where needed Classical.choice). BranchingBlocksSource.lean specializes to the certified original-source laws and conjoins the guard with the existing direct-block halting equivalence. Initial source-closure CI 45420137632 caught a remote transcription typo (Nat.one_mul in place of Nat.mul_one), corrected to the locally accepted expression; full source closure subsequently passed in run 45421542043. The old finite-budget signed cone remains useful for arbitrary branching away from this special family.

## Signed-residue method (SignedCone.lean and HighSigned.lean)

Represent the authentic section counters as x=P A+u, y=P B+v, P=2^b, where A>=0, B>=1, and either A>=1 or u>5. Offsets u,v are arbitrary signed integers. The executable checker never evaluates A or B. Its guard 2(|u|+|v|+8)<P ensures x>5, y>=8 and the rounded sum Q>P/2. With o=(u+v) mod 2, exact nonzero valuation w of u+v+o and w+1<=b, the source Q has valuation w and is not a pure power. The existing necessary parent grammar therefore enumerates all reachable parents.

Each direct edge (when v even) charges one bit, updates offsets to (u+v-2,(v-2)/2), and leading coefficients to (2(A+B),B). Each high depth n charges n+2 bits, with n+2<=w and the correct parity; update signed offsets

    u' = (u+v+o)/2^(n+1)-2-o
    v' = (u+2v-u'-7-3n)/2,

and coefficients

    A' = 2(A+B)
    B' = 2^(n+1)(A+2B)-(A+B).

Both leading coefficients remain positive. Exact small-integer validity tests ensure integral child offsets. The checker accepts only if all admissible children accept, or if the actual odd-right forbidden-image residue is reached. Thus a finite branching tree certifies unreachability for **all** leading coefficients compatible with the representation. SignedCone.check_sound proves this under explicit ParentContract and forbidden-image premises. It is not restricted to positive negative shadows.

For high stop parameters j>=2,m>=2, take b=2m+2, A=0, B=j+3, u=2j+3, v=-(j+3m+5). Alternatively choose any r<=b, center these offsets modulo 2^r, and use adaptiveExcluded. The source stopping equation implies y>=2^b, so the centered residue representation is sound at every admissible precision; no triangular condition j<=3m remains. Smallness and exact valuation still determine whether a certificate accepts, and the pure-power residual case is not decided by this method.

The adaptive checker is periodic in a **coupled lattice**, with sufficient nonnegative parameter displacements U,V satisfying

    2^r | 2U,    2^r | U+3V.

This lifts entire branching predecessor trees, not only forced chains. At (j,m)=(40,5), r=10, both possible first parents have forbidden odd-right residues. Lean kernel reduction checks adaptiveExcluded 2 10 40 5=true; the general lattice theorem gives

    adaptiveExcluded 2 10 (40+512t) (5+512t)=true    for every t>=0.

The seed is outside j<=3m and survives the four-sector single-parent normalizer. This is not a claim that it survives every earlier integrated high sieve. The generic checker soundness and this infinite branching family are the substantive deliverables, rather than a list of isolated residue counts.

## Verification boundary

SignedCone.lean and HighSigned.lean compiled locally against the independently compiled HighShadowArithmetic.lean, with Lean 4.36.0-rc2. All seven printed theorem profiles contain only standard axioms. HighSignedSource.lean instantiates the actual parent grammar and forbidden-image theorem from Agent13's existing AffineConeLowStop import closure. Its exact source compilation is pending (local shell has no GitHub DNS access). No new CI workflow was created. The existing M16 source closure workflow now has a sourceBranchingBlocks target. Do not count the original-source corollaries as source-certified until they compile.

## Earlier positive-shadow bridge

HighShadowArithmetic.lean also provides the first-parent negative-shadow specialization for 2<=j<=3m. Let E=2^(2m+2)(j+3), o=(3m+2-j) mod 2, c=3m+2-j-o. Then x+y+o=E-c and x+2y=2E-6m-7. The direct shadow is (3m+4-j,(j+3m+7)/2), high depth n shadow is (C,(6m+14+3n-C)/2) with C=c/2^(n+1)+2+o. The arithmetic proof compiled standalone; HighShadow.lean's actual NegativeShadow source instantiation is pending. Local interpreted evaluation of copied checker definitions accepted 758/767 j at m=256, leaving nine unresolved. That finite scan was a feasibility diagnostic and not a global proof.

## Remaining mathematical gap

The signed cone covers a wider unbounded parameter domain and provides a proof-carrying all-parent certificate, but not a universal termination or precision bound. The unresolved high and low parameter existentials remain unbounded. A naive universal negative-shadow termination theorem is false: the direct shadow at right coordinate 2 has an infinite direct path (x,2)->(x+4,2). Whether reachable from specific parameter domains requires separate analysis. The pure-power rounded residue and small original left-coordinate cases also need separate treatment. No Machine C or BB(6) decision is claimed.


## Exact pure-power predecessor fan and shifted phase reduction

PurePowerFan.lean proves an exact iff against all five arithmetic predecessor sectors, including both special a=0 and a=1 branches. For odd x and Q=x+y+(x+y)%2=2^v with v%2=1-o, o=(x+y)%2, the bounce fan has exactly the exponent interval 1<=d, 2d+1<=v. Its left coordinate is a=4^d-2-o and its mass equation is 2k+a+7+3(v-1-2d)=x+2y. Every such d has a feasible parent for y>=8. The remaining member is a direct edge if o=1, or the a=0 exceptional edge if o=0. PurePowerStopData.lean shows positive-index pure stops satisfy the required parity, r=v%(2m+2)>=3, y>=2^(v-1), and j+3=2^r modulo 2^(r+2m+2). This last shift is valid at an exponentially larger precision than r.

PurePowerPhases.lean proves that with h=(v-1-2d)/2 the exact parent equation is k+j+4+2o+3h+2^(2d-1)=2^v, and y<=2k+1. For b<=r+2m+2 and b+4<=v, let J be 2^r modulo 2^b. The signed phase of every bounce parent is (2^(2d)-2-o, -J-1-2o-3h-2^(2d-1)) modulo 2^b. Compute binary powers with truncated exponent comparisons; no huge counters need to be materialized. For 2d>=b+1 the phase depends only on h mod 2^b and o. The exceptional zero parent has phase (0,-J-3 floor(v/2)). The positive-index pure root's direct parent is always unreachable by a forced direct step to a forbidden odd-right image.

PurePowerSource.lean connects the exact arithmetic fan to the existing complete_section_inverse, then applies Agent42's modular cone to produce an exact pruned reachability iff for positive-index pure-power stops. All arithmetic modules compiled locally without custom axioms; raw_parent_iff was locally checked against the verbatim source criterion definition. Full source integration dispatched via sourcePurePower; success pending. Python exploration of 12-bit tail phases (J=0) gives 1208/4096 and 1250/4096 residual classes for o=0,1. These counts are computational, not claims that residual phases are reachable. The actual Lean source module includes the equivalent census. No claim of a universal nonhalt proof.

BranchingBlocksSource passed full source closure in [run 45421542043](https://github.com/FlareZ123/bb6/actions/runs/45421542043).



## Valuation-bounded exact compressed memoization

`ValuationParents.lean` gives an exact predecessor list with at most v₂(Q)+3 attempted candidates when y≥8, where Q=x+y+(x+y) mod 2. It includes the direct and exceptional zero/one parents and at most one regular parent per valuation depth. Its equivalence to the original section predecessor relation was checked locally against the verbatim arithmetic definitions. `DirectJump.lean` supplies a ranked macro edge for a forced direct prefix.

`PurePowerRawParent.lean` isolates the exact arithmetic bridge `RawParent ↔ sectionPreimageCriterion` using only `PurePowerPhases` and the original `FullSectionInverse`. This is the minimal source-predecessor interface needed by the memoizer; it avoids importing the heavier pure-power modular-cone analysis into the proof-only closure.

`CompressedMemo.lean` proves that the valuation-bounded parent list preserves the exact source predecessor relation, that compressed direct jumps preserve reachability and rank, and that the memoized exclusion procedure is sound and complete. In particular, `compressedDecision_iff` is an exact decision theorem for an arbitrary section point, while `blank_halts_iff_compressed_memo` gives an exact original blank-root low/high stopping criterion with an additional bounded high-stop guard. This criterion does not decide Machine C: the remaining parameter existential is still unbounded.

The optional 18-case pure-power diagnostic is isolated in `CompressedMemoAudit.lean`; it is not imported into the theorem closure. `PurePowerSource.lean` retains the stronger source-fan and pure-power modular pruning theorems under its separate `sourcePurePower` acceptance target, which remains pending.

The proof-only `sourceCompressedMemo` original-source closure passed CI [run 45485987157](https://github.com/FlareZ123/bb6/actions/runs/45485987157), compiling the repaired `ExactMemo`, isolated `PurePowerRawParent`, and core `CompressedMemo` proof chain. The subsequent experimental high-seed declaration has been removed from the proof-only module; the accepted core is restored.

Agent 1's [M8 source certificate](../agent1-c-m8-trace/README.md), theorem `all_terminal_below_rank_unreachable` (original-source CI [run 41670233031](https://github.com/FlareZ123/bb6/actions/runs/41670233031)), proves that every immediate terminal section state `(a,k)` with `secNext (a,k)=none` and `a+2*k<1,048,525` is unreachable from the genuine blank section `(5,1)` at every return time. This universal cutoff subsumes low/high stopping seeds in that mass range; do not re-prove them.

The first low-stop parameter beyond the cutoff not already caught by `sourceBad` is `m=10`, target `(1, 8,388,574)`, mass `16,777,149`. The first pure-power high-stop target beyond the cutoff is `r=3,s=2`, with `m=1`, `v=23`, `j=493,445`, `k=7,401,715`, target `(986,893, 7,401,715)`, mass `15,790,323`.

## Structurally reducible exclusion certificates

`KernelCone.lean` retains exact compressed parents on the high-right region y≥8 and all four sound exclusion guards. It does not use a hash map, native evaluation axiom, or the complicated small-right enumerator. A small-right node not rejected by a sound guard returns false. Induction on fuel proves `treeExcluded_sound_of` under the exact-parent and guard contracts, then `treeExcluded_sound` specializes to the already proved source laws. `treeExcluded_children` permits compositional certificates for larger inverse trees.

For the first low-stop target m=10, the exact arithmetic tree closes in 25 nodes at depth seven. Local Lean 4.36.0-rc2 accepted `treeExcluded 24 7 (1,8388574) = true` using `decide +kernel`; axiom profile `[propext, Quot.sound]`. The source-level theorem `lowStop10_not_reachable` passed original-source [CI 45497710445](https://github.com/FlareZ123/bb6/actions/runs/45497710445), completing this exact low-stop exclusion.

The earlier 256-fuel native experiment did not reach evaluation: CI [45493341903](https://github.com/FlareZ123/bb6/actions/runs/45493341903) rejected the nonexistent `Lean.Elab.Tactic.NativeDecide` module. A local exact arithmetic port of the new checker evaluates the high seed at fuel 256 to false and fuel 540 to true. Independent Python traversal found 16,262 nodes, no repeated ancestors, no unresolved leaves, and maximum depth 534. The single full kernel reduction timed out; the diagnostic is isolated in `KernelConeAudit.lean`. The inverse-tree computation remains computational evidence, but the target itself is now source-certified excluded by the universal terminal-mass cutoff below.

## Universal terminal-mass cutoff extension (source accepted)

Independent exact forward evaluators in C++ and JavaScript agree: after the already certified return 150052 at (621619,213453), another 2,246,326 returns lead to (7215288,4780931) at return 2,396,378, mass 16,777,150. The submitted certificate consists of 225 closed kernel checks in 15 parallelizable modules, using the original `M8TraceBridge.runFast`; there are no native-evaluation axioms. Each segment is at most 10,000 returns. A local two-segment composition test with the verbatim runner definitions compiled and reported only propext. `Agent12TerminalCutoff.lean` composes these segments with the already certified M8 prefix and gives the generic `terminal_below_live_endpoint` and specialization `all_terminal_below_16777150`. The new theorem excludes **every** source-defined immediate terminal target of mass less than 16,777,150 at all times, including both the first pure-power high seed and m=10 low seed, without inspecting their individual inverse trees. The full original-source proof passed the existing M16 workflow's `sourceTerminalCutoff` target in [CI 45498220565](https://github.com/FlareZ123/bb6/actions/runs/45498220565), certifying both the live endpoint and the universal cutoff.

## Structural obstruction to periodic growth

[The aperiodicity theorem](../../results/2026-11-24-machine-c-aperiodic-section-itinerary-agent12.md) proves that every infinite successful Machine C section orbit has a non-eventually-periodic complete branch itinerary. The proof derives a primitive binary repetend with a severe totient/index restriction, classifies its denominator as 15, and eliminates the resulting shift cycle (2,1,1) by parity-aware integrality modulo 17. `AffinePeriod.lean` checks the affine increment theorem and final modular contradiction in Lean 4.36.0-rc2; the complete classification is written mathematics, not yet fully formalized. Do not mistake this for an infinitude or nonhalting proof.

[The semilinear obstruction](../../results/2026-11-24-machine-c-semilinear-obstruction-agent12.md) extends this to a no-go theorem for every nonempty terminal-free forward-closed semilinear set of section counters. Prepared halting rays exist in every congruence cone via finite modular controllability and exact integer lifting; no infinite orbit can lie in finitely many affine lines. `ModularSteering.lean` checks the algebraic identities. `halting_ray.py` constructs exact rays, checking all guard inequalities as affine functions of the ray parameter. Its 24 demonstration cases and 72 independent sample replays pass. The full structural theorems are written proofs, not fully formalized, and do not settle the blank orbit.

[Polynomial-congruence obstruction](../../results/2026-11-24-machine-c-polynomial-congruence-obstruction-agent12.md) strengthens the semilinear result: any infinite orbit has ratios outside every polynomially narrowing union of finitely many directions infinitely often. A bounded block of near-zero visits supplies binary-shift modulus larger than the mass band, hence a small endpoint and fixed label word uniquely recover starting mass. The word count is polylogarithmic, giving a contradiction to mass-crossing frequency. `Concentration.lean` verifies the exact modular injectivity lemma. Leading homogeneous polynomial signs and the congruence-cone halting-ray theorem then rule out nonempty terminal-free forward-closed polynomial-sign/fixed-congruence Boolean sets. Written proof, not an end-to-end Lean theorem.

## Constant-candidate closed-form bounce (24 November)

[`ClosedBounce.lean`](ClosedBounce.lean) eliminates recursive bounce simulation while preserving the exact section clock. Set (B=k+b), (b=3) for odd middle counter and (b=4) for even. The first exit depth is the least (n) with (c+2B+3n\le 2^{n+2}B). It lies among the three candidates beginning at `max(0, log2(c+2B)-log2(B)-2)`. At that depth the counters are (K=2^nB-b), (C=c+2k+3n-2K). The odd clock is (c+n), the even ordinary or terminal clock is (c-2n-3), and the even exceptional (C=4) clock is (c-2n-2). Small input guards are handled separately. Theorems `closedBounce_eq` and `closedSection_eq` compiled locally against verbatim copies of the source definitions with standard axioms only. The original-source CI target `sourceClosedBounce` is submitted separately. This accelerates exact arithmetic; it does not close the unbounded blank-orbit decision.

## Endpoint-only ordinary word certificates

For section mass M=a+2k and left counter A=a, define G=M-A, and for a positive ordinary shift r write o=M mod 2. The affine branch, including the direct r=1 case, is
```
M'=M+3r+1
A'=2^r(A+2+o)-M'-2o.
```
For a word with total shift R, compose the affine equations to A'=P A-Q M+C, M'=M+W, P=2^R. If the initial A and M have equal parity, M≥8P, and the composed endpoint satisfies A'≥0 and M'-A'+4≥20P, then **every edge in the word is a genuine ordinary section edge**. No intermediate guard replay is required. The proof runs backwards: each ordinary affine step with sufficient mass and a valid output gap ≥16 has valid input counters, the correct direct/regular branch inequalities, and G'+4≤2^r(G+4). The exact inverse theorem then supplies the source edge. Induct backward through the word to propagate the endpoint gap budget. The coefficient composition theorem supplies a constant number of endpoint arithmetic operations after the word coefficients are precomputed.

`WordBlock.lean` contains the complete kernel-checked generic certificate, including decoding and parity, with standard axioms only. `WordBlockSource.lean` instantiates the arithmetic edge law with the existing complete_section_inverse theorem; the instantiation compiled locally against its verbatim predicate. The original-source edge law is included in the successful sourceWordRunner CI closure. The condition is sufficient, not necessary: fallback to the exact single-return evaluator whenever the margins fail. This is a proof-oriented accelerator, not an infinite-orbit claim.

The constant-candidate closed-bounce proof has now passed original-source CI [45502202006](https://github.com/FlareZ123/bb6/actions/runs/45502202006).

## Certified affine-word runner and computational terminal search

[WordRunner.lean](WordRunner.lean) implements cached, proof-carrying affine plans, endpoint acceptance, dyadic-prefix prediction, and an arbitrary-budget runner that falls back to the exact single-return map. The generic theorem `runBudget_eq` holds for **every predictor**, not just the dyadic one. It compiled locally against WordBlock.lean under Lean 4.36.0-rc2, with only propext, Classical.choice, and Quot.sound. [WordRunnerSource.lean](WordRunnerSource.lean) connects the runner to the actual source section map via WordBlockSource and ClosedBounce. The original-source closure passed [CI 45522080605](https://github.com/FlareZ123/bb6/actions/runs/45522080605) at commit 50c1c49915e6f7799fa954ee4600d266b7e16b43.

[block_c.cpp](block_c.cpp) is the independent fixed-width exploratory implementation. Build with `g++ -O3 -std=c++20 block_c.cpp -o block_c`; arguments are starting return, a, k, ending return, prefix bits (defaults 0,5,1,1000000000,12). The first billion returns agree with the single-return evaluator: (358994343,3320495488), mass 6999985319. The second billion ends at (4673821904,4663082990), mass 13999987884. The block run took 2.48 s for the first billion versus 11.73 s for the single-return implementation in this environment. Independent evaluators agree at every overlapping billion-return checkpoint. The accelerated search passed 125 billion returns, endpoint (838842302846,18079374398), mass 875001051642, with no terminal event. These are computational endpoints, not kernel-certified finite witnesses or nonhalting claims. The existing kernel-certified terminal cutoff remains 16777150 until a stronger source certificate is accepted.

## Exact primitive-clock acceleration

[OrdinaryClock.lean](OrdinaryClock.lean), [CountedOrdinary.lean](CountedOrdinary.lean), [WeightedWord.lean](WeightedWord.lean) and [WeightedWordSource.lean](WeightedWordSource.lean) extend the endpoint-only ordinary block theorem to exact CLine calls and primitive moves. For A=a, M=a+2k, X=successor left counter, o=M%2, ordinary positive shift r, six times the primitive cost is the polynomial

    -4 A²+16 A o-22 A+4 M²-4 M X-8 M o+24 M r-M
      +4 X²-8 X o-12 X r+11 X-96 o r+96 o+36 r²-51 r+39.

The CLine call count is M-A+r+o(3-3r). Substitution of affine prefix forms yields six precomputed quadratic coefficients and three linear coefficients for a whole block. The kernel theorem block_raw_execution uses the original Agent47 ThinGatewayCounted/CRawCountBridge literal-machine path, so it has no unchecked source simulator assumption. Full original-source CI [45539039923](https://github.com/FlareZ123/bb6/actions/runs/45539039923) passed at 510314bf7b68d54f0334713594ad002efdc23efd.

[clock_block.cpp](clock_block.cpp) implements this polynomial and independently tests every pair a,k<128 against a literal CLine interpreter and 100,000 random pairs (99,976 accepted blocks at 12 bits). Its fixed-width explorer has checked 128-bit clock accumulation and a 2^41 mass cap. [unweighted.cpp](unweighted.cpp) is the smaller 14-bit-table endpoint-only explorer. These are computational implementations, not kernel evaluations of the full traces. The three relative weighted segments were:

| Returns | Endpoint (a,k) | Primitive nonhalting moves in segment | CLine calls in segment |
|---|---|---:|---:|
| 0 to 100,000,000,000 | (275133587597,212433398910) | 5444467942584747322477887332687250 | 17500061408415500929561 |
| 100,000,000,000 to 125,000,000,000 | (838842302846,18079374398) | 5189235901283050767015204543304192 | 9843743679985846229590 |
| 125,000,000,000 to 200,000,000,000 | (740396216379,329803495692) | 32922224457075400481166569706123508 | 42656624824206565090781 |

Adding the initial 14 primitive moves and one CLine call to the relative sums gives 43555928300943198570659661582114964 primitive moves and 70000429912607912249933 calls at the 200-billion-return checkpoint (mass 1400003207763). The amended explorer includes this initial correction automatically only when started at return 0, (5,1). No halt was observed; this is not a new kernel-certified mass cutoff.

## Uniform dyadic ancestry sparsity

The new [Haar-null ancestry and finite-sieve density theorem](../../results/2026-11-25-machine-c-dyadic-density-completeness-agent12.md) proves arbitrarily small admitted fractions of high-stop j residues uniformly in every m, and of the low-stop m tail, by analyzing the critical affine IFS on Z₂² × parity. Its central mechanism is arbitrary multiplicity of coincident two-return image cylinders combined with a uniform-marginal argument. The algebra, collision construction and closure theorem in DyadicAncestry.lean, DyadicAncestryBridge.lean and DyadicAncestrySource.lean passed original-source CI [45540503720](https://github.com/FlareZ123/bb6/actions/runs/45540503720); Haar measure and convergence are paper proofs, not Lean theorems.

The experimental [dyadic_sieve.cpp](dyadic_sieve.cpp) finite BFS includes every exceptional birth. At K=13 it admits 50,610,768 of 134,217,728 residue triples, 2,824 of 8,192 low-line residues, and at most 3,464 of 8,192 residues on any high-family line. These are overapproximation counts, not reachability or machine decisions. Negative-shadow experiments also found paths surviving beyond the available exponent precision for some low stopping indices. Do not assume uniform pointwise extinction from the density theorem.
