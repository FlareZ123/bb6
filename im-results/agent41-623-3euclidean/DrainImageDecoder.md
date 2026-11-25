# Direct digit inversion of the #623 positive-budget drain image

Theorem file: [DrainImageDecoder.lean](DrainImageDecoder.lean). The arithmetic decoder was independently kernel-checked with Lean 4.36.0-rc2 (b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a); its printed axioms are propext, Classical.choice and Quot.sound. The exact source envelope is supplied by Agent49. The complete source-imported chain (DrainImageSource.lean, ExactParentRays.lean, DrainImageAP.lean, FatalBandSource.lean, DrainImageDensity.lean, and FatalDensitySource.lean) compiled against the pinned unmodified Cryptids table in [CI 45552009439](https://github.com/FlareZ123/bb6/actions/runs/45552009439), using Cryptids commit c86f15861709b76042998c5211c7b2f83991621b and Lean 4.35.0-rc4. The workflow captured the #print axioms output and rejected sorryAx or native_decide; the run passed. This source-certifies the positive-density predecessor-free terminal-row theorem, not the full nonhalting of #623.

## Result

For E(0)=0, E(3q)=E(q-1) (q>0), E(3q+1)=4+E(q), E(3q+2)=2+E(q+1), define F(b)=3b+E(b). The executable inverse satisfies, for all y,b in Nat,

    inverse y = some b  iff  F(b)=y.
    inverse y = none    iff  forall b, F(b)!=y.

This gives a direct most-significant-digit inverse with no candidate scanning or binary search on the block counter. The exact residual path is encoded by a ternary word of length k, with digits 2-r for residue r of each visited block. Writing U for that word, T=(3^k-1)/2, and c for the digit charge (#1 minus #2), the identities are b=2U-T, E=2k+2c, F=2(3U+c)-3T+2k. Nonzero words have nonzero leading digit. The three leading-digit intervals of 3U+c are disjoint; the decoder removes a digit and divides the place value by three. The output itself fixes k by parity and the strictly separated length bands. The band search uses a linear number of repunit updates in the bit length of y.

Two global image restrictions follow:
* F(b+2)>=F(b)+2, with equality **iff** b mod 3=1. Therefore among any y,y+2,y+4 at least one is absent from the image.
* For every k>=0 and 1<=j<=k+5, F never equals 9*T(k)+2*j. This follows from the bound F<=9*T(k) for length k, and F>=9*T(k-2)+2*k+8 for length k>=2, with k and F of equal parity.

These are quantified statements, not extrapolations of finite scans. The proof builds on Agent49's correction growth and strengthens the parity-specific image monotonicity to exact minimum-gap classification. The existing near-power inverse is a special case of this general decoder.

## Relevance and limits

Agent49's inverse window proves y=z+F(b) for a successful original drain returning (x,y) with x>=2*(y.log2+1). In the large-first-coordinate sector, the two candidate shifts are z=2,3 if y is even and z=5,0 if odd. Missing both shifted images is a sufficient no-parent criterion, potentially excluding infinitely many entire vertical rays from the blank-root orbit. The new adapter uses the exhaustive six-branch envelope: the axis has y=7 or 14, the diagonal has A=0 and is incompatible with the large-first condition, and the four other branches give the two shifts above by parity. Thus for y>14, if both shifted inverse calls fail, no original predecessor exists, so no authentic blank-root orbit index can hit any (x,y) with x>=2*(y.log2+1).

Set y=9*T(k)+2*j+2 for even k, or y=9*T(k)+2*j for odd k. For k>=2 and 1<=j<=k+3, all three rows y,y+2,y+4 are in a gap for one shift. The no-three theorem gives at least one row missing the other shift too. The theorem `band_root_exclusion` formalizes the resulting unbounded family of entire excluded rays, conditional on the original source adapter passing CI. These are predecessor-free rays rather than finite orbit scans. No halting-family exhaustion or BB6 upper bound follows yet.

### Exact large-counter predecessor rays (2026-11-25)

[ExactParentRays.lean](ExactParentRays.lean) upgrades the necessary gate to an equivalence. For y>20, x even, and x≥2(log₂ y+1), let J(b)=drift(b), A=x−J(b). Decode two parity-compatible image values:

| y parity | left inverse and parent | right inverse and parent |
|---|---|---|
| even | b=inverse(y−2), (A+b,b−2) | b=inverse(y−3), (b+1,A+b−3) |
| odd | b=inverse(y−5), (A+b+2,b−3) | b=inverse(y), (b−1,A+b−2) |

A failed inverse produces no candidate. Every successful inverse gives an actual valid predecessor with even first counter. Left satisfies a>d, right a<d, so distinct. No further search or forward reevaluation is needed. Exact indegree (0,1,2) is independent of sufficiently large even x in each row. Sufficiency uses the certified positive trace at budget n=log₂ y+1, giving |J|≤n; A≥n then ensures the drain reconstructs the target. Completeness follows from the source envelope. Having a parent is not equivalent to blank-root reachability.

First pinned CI [45524233943](https://github.com/FlareZ123/bb6/actions/runs/45524233943) accepted arithmetic decoder and gate modules, but failed on Mathlib notation conflict (0<inverseBudget parsed as 0 <i nverseBudget). Corrected syntax. New module typechecks locally against exact original evaluator/drain/highLevelNext definitions and interface stubs for prior theorems; full pinned CI pending. Stubs not committed.

### Quantified terminal-row density (2026-11-25)

[DrainImageAP.lean](DrainImageAP.lean) proves that no three drain-image points form an arithmetic progression with positive even step below eight. It also constructs an injective family of doubly blocked row indices d(c), satisfying d mod 6 in {1,2} and d <= 59049c + 88589 + 4(log2(19683c+29523)+1). The separate [FatalBandSource.lean](FatalBandSource.lean) maps such rows to the original immediately halting states D(d+2,d) for even d and D(d+5,d) for odd d and proves exclusion from every authentic root index. The stronger counting argument below supersedes the injection's asymptotic density estimate.

[DrainImageDensity.lean](DrainImageDensity.lean) gives a uniform finite lower bound, independent of any finite run or probabilistic model:
`2*N <= (goodTerminalRows N).length + 6`.
The list is duplicate-free; each member d is above 14, below 18N, satisfies d mod 6 in {1,2}, and is blocked.

Proof: group all block counts except 0,1,3 into triples (3q-1,3q+1,3q+3) for positive q. Within each triple the exact image offsets are 0,8,10. The parity of all three blocks is the same. For each target parity, the respective shifted images have three distinct residues modulo 6, hence only one can satisfy its terminal residue (2 for even, 1 for odd). All possible gate hits from b with 3b<=d<18N are covered by the two selected rows in each of the 2N triples q=1,...,2N, together with the six small terminal rows <=14. Thus at most 4N+6 of the 6N terminal rows below 18N can be small or unblocked. The remainder is at least 2N-6. This is an exact Lean List-cardinality argument (no asymptotic estimate or sampling in the theorem).

[FatalDensitySource.lean](FatalDensitySource.lean) instantiates the four excess laws and the source-level terminal predicate to show that every selected row gives an actual synthetic immediate halter with no predecessor, and is excluded at every authentic root index. The finite count implies lower asymptotic density at least 1/9 among all nonnegative row indices, or at least 1/3 relative to this particular two-residue terminal family. It does not say 1/3 of all fatal states are excluded. The generic finite-density theorem goodTerminalRows_count and its source wrapper terminal_density are now accepted against the original machine in CI 45552009439. For every N, at least 2N-6 distinct rows below 18N satisfy the terminal congruence and are blocked; each gives a terminal macro-state with no predecessor and no authentic root index. Consequently the parameter set has lower density at least 1/9 among all row indices (at least 1/3 relative to rows congruent to 1 or 2 mod 6). The audited workflow rejects sorryAx and native_decide. This is an exclusion theorem, not a proof that the root never halts.
