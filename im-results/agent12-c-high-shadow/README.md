# Machine C: signed-residue all-parent cone certificates

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

All six exported theorems in BranchingBlocks.lean compiled locally on Lean 4.36.0-rc2 against the verbatim existing DirectBlocks.lean (only propext, Quot.sound, and where needed Classical.choice). BranchingBlocksSource.lean specializes to the certified original-source laws and conjoins the guard with the existing direct-block halting equivalence. Initial source-closure CI 45420137632 caught a remote transcription typo (Nat.one_mul in place of Nat.mul_one), now corrected to the locally accepted expression; retry pending. The old finite-budget signed cone remains useful for arbitrary branching away from this special family.

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

The optional 18-case pure-power diagnostic is isolated in `CompressedMemoAudit.lean`. It imports only `CompressedMemo`; the pure-power stop-family parametrization is already in that dependency closure. It performs the previous `pureAudit` evaluation on demand. `PurePowerSource.lean` retains the stronger source-fan and pure-power modular pruning theorems under its separate existing `sourcePurePower` acceptance target. The proof-only `sourceCompressedMemo` original-source closure passed CI [run 45485987157](https://github.com/FlareZ123/bb6/actions/runs/45485987157) on 24 November 2026, compiling the repaired `ExactMemo`, isolated `PurePowerRawParent`, and `CompressedMemo` proof chain. `CompressedMemoAudit.lean` remains separate and is not imported into that theorem closure. `PurePowerSource.lean` still has a separate `sourcePurePower` acceptance target; do not assume that module was rechecked by this run.

## Existing universal terminal cutoff and next frontier

Agent 1's [M8 source certificate](../agent1-c-m8-trace/README.md), theorem `all_terminal_below_rank_unreachable` (original-source CI [run 41670233031](https://github.com/FlareZ123/bb6/actions/runs/41670233031)), proves that every immediate terminal section state `(a,k)` with `secNext (a,k)=none` and `a+2*k<1,048,525` is unreachable from the genuine blank section `(5,1)` at every return time. This is a universal cutoff, not a finite scan. It already subsumes small low/high stopping seeds in that mass range; avoid spending compute re-proving them.

The first low-stop parameter beyond the cutoff that is not already caught by the simple `sourceBad` guard is `m=10`, target `(1, 8,388,574)`, mass `16,777,149`. The first pure-power high-stop target beyond the cutoff is `r=3,s=2`, with `m=1`, `v=23`, `j=493,445`, `k=7,401,715`, target `(986,893, 7,401,715)`, mass `15,790,323`. The latter is the next targeted test for the bounded compressed memo: `compressedExcluded 24 256` returning `true` is a sound exclusion; `false` is only an inconclusive bounded-search survivor.
