# #429 branch-29 signed inverse drift exclusion

This is a reduction of the signed inverse problem, **not** a closure of branch29 or a source-machine nonhalting theorem. It builds on [Agent 18's negative dyadic analysis](../agent18-429-root-invariants/NEGATIVE_DYADIC.md) and the exact modular guards of [Agent 33's inverse kernel](../agent33-429-24/BB429InverseKernel.lean).

For the signed inverse model let a=-u-3, b=6-4u-D, and R=-2a-b=6u+D. The three uncompressed inverse rules are F(a,b)=((a-3)/2,b+a), E(a,b)=((4a+b-14)/4,b/2), S(a,b)=((4a+b-26)/4,(b+4)/2), with the six existing modular Bad leaves and integrality guards. These are signed offset rules; they omit positive affine lift bounds. E and S require b=2 mod4 and yield an odd second coordinate, forcing F next on an infinite path. Thus the compressed block system has only:
- F: u'=u/2, D'=D+3u+3, R'=R+3 (u even)
- EF: u'=u+(D+8)/8, D'=D/4+4, R'=R+10 (u odd, 8|D)
- SF: u'=u+(D+20)/8, D'=D/4-1, R'=R+14 (u even, D=4 mod8).

**Theorem.** Every hypothetical infinite signed inverse path from (29-32c,55-64c), c>=4, after the forced first F, admits a compression into these blocks staying in u>0, D>=2, D!=4. Moreover both standalone F and paired blocks must occur infinitely often.

Proof: first F is forced since initial b=3 mod4; its endpoint has u=16(c-1), D=32(c-1)+18. F preserves the region. EF has D>=8 and D'>=6. SF has D>=12 and D'>=2; D'=4 would require D=20, giving u'=u+5 odd and therefore a' even, b'=6 mod8, a Bad leaf. Consequently D=0 and D=4 are inaccessible at compressed positions. The four alternating drift rays in the prior analysis are rotations of these two boundary lines: the other two rays occur at the intermediate E/S positions. In the safe region every pair strictly decreases D; every standalone F strictly decreases u. Neither can persist alone forever. For paired blocks also 4(D'-6)<=D-6, giving a logarithmic bound on uninterrupted pair-run length for D>6 until D<=6; at D<=6 another pair is impossible. Uninterrupted F-run length is bounded by the binary valuation of positive u.

The Lean proof checks the exact signed modular predicates, algebra, forced compression and the infinite-path theorem (including recursive selection of compressed indices). It does not certify the source-to-signed lift nor show that infinitely many interleaved F and paired blocks cannot occur. The remaining task is to rule out such mixed paths and give a finite precision bound fitting the actual feeder exponent. A finite modulus graph alone appears inadequate: modulo 8 through 128 the exploratory compressed graph has one mixed recurrent SCC (not a proof of obstruction).

## Reproduction
Restore SignedDrift.lean using reconstruct.py, run lean SignedDrift.lean under Lean 4.36.0-rc2. All eleven printed axiom profiles are subsets of propext, Classical.choice, Quot.sound. SHA256 94a1a7a4c25f98031b8d758048c05430ab5894bb51e2c144f8ee46f6f7846a0e. No new finite k scan is claimed.

## Quantitative finite precision lifting

Added SignedLift.lean, locally Lean checked. For signed a<=-3,b<=3 define rank R=-2a-b. Every Raw child satisfies the same signed coordinate bounds and R'<=R+11. Define Closed d as the complete depth-d signed tree ending in Bad leaves (or even no-child cases); signedCert is an executable Boolean with kernel-checked soundness. For m divisible by32 and m>=R+11d+16, and positive integer K,L, a closed signed tree excludes the positive state (K*4^d*m+a,L*4^d*m+b) under the exact ReachLaws (Bad exclusion and odd/even predecessors). Induction loses only two bits of precision per raw edge: coefficients (K,L) become (2K,4(K+L)) for F, (4K+L,2L) for E/S, with scale divided by4. Rank bound keeps actual states above original positivity guards, and m mod32 preserves all Bad predicates. This gives an explicit finite precision bound rather than an asymptotic lift.

Specialized to actual feeder q+c=3*2^N (N=n-5), c>=4, a=29-32c,b=55-64c. If e>=5, 2d+e<=N, and 2^e>=128c-97+11d, signedCert d a b=true is sufficient to exclude (32q+29,64q+55). No evaluation of the huge 2^N is needed in the signed tree. The Lean specialization branch29_lift is checked under ReachLaws. SignedSource.lean connects those laws to exact repo BB429NewResidue and root-mod lemmas. The complete manual workflow passed twice on 2026-11-24: run #45464411810 compiled the pinned rank/modular dependencies, reconstructed and compiled SignedDrift and SignedLift, compiled the initial SignedFRunParity theorem, and compiled SignedSource; run #45466029696 repeated the dependency closure after the refined EF/SF endpoint tables were added. The source adapter and all current SignedFRunParity theorems are CI-checked. This validates the theorem dependency closure, not any particular signed-tree certificate or all-k exclusion.

The all-k objective is now a clear sufficient target: prove the signed trees close with d,e satisfying these bounds for all c=3k+4,N=122+128k. No claim of that proof. The source-independent finite precision transfer and executable checker are checked with only standard Lean axioms.

## Exact first-pair classification on the feeder line

The signed F-run reduction is now formalized in
[`SignedFRunParity.lean`](../agent18-429-root-invariants/SignedFRunParity.lean).
For the post-forced-F feeder state
`u=48t, D=96t+18`, it proves the exact equivalence

`InitialPairAvailable t ↔ t % 4 = 3 ∨ t % 16 = 0`.

Here `InitialPairAvailable` means that some finite run of standalone F
blocks reaches an endpoint satisfying either the EF guard
(`u_endpoint` odd and `D_endpoint ≡ 0 mod 8`) or the SF guard
(`u_endpoint` even and `D_endpoint ≡ 4 mod 8`). Equivalently, with
the original parameter `t=k+1`, a first pair is available exactly
when `k ≡ 2 (mod 4)` or `k ≡ 15 (mod 16)`.

The proof strengthens the parity table to endpoint residues modulo 4,
uses the exact telescoping identity
`D_m + 6u_m = D + 6u + 3m` and `u=2^m u_m`, and supplies explicit
four-F EF and six-F SF witnesses for the two surviving classes.
The file imports only `Lean`; its local Lean 4.36.0-rc2 compilation
succeeded. The printed axiom profile for the equivalence is
`[propext, Classical.choice, Quot.sound]`.

**Scope:** this is an exact theorem about the compressed signed inverse
system's initial F-spine, not a positive-root exclusion and not a
closure theorem for the full branching inverse tree. The 14/16
complement is ruled out only for the existence of an EF/SF pair on that
initial F-spine. The remaining two parameter classes, and the branches
that choose or skip an available pair, remain to be resolved.

The same file now also proves refined EF/SF endpoint tables conditioned on
the previous pair endpoint modulo four. These distinguish the possible
`m mod 8` and `u_m mod 4` combinations after EF and after SF, rather
than retaining only the even-run conclusion.

## Full signed-tree scan (computational evidence, not proof)

`signed_tree_experiment.py` transcribes the exact integer `allowed`,
`bad`, and F/EF/SF block rules from `SignedDrift.lean`, then explores
the complete branching tree with cycle detection and memoization. Its
default scan covers `t=1,...,2^20`, i.e. feeder parameters
`k=t-1=0,...,2^20-1`.

Observed in that scan:

- Every tree terminated; no repeated-state cycle was found.
- Every terminal state had at least one algebraically guarded child, but
  all such candidate children were Bad. There were no no-guard leaves.
- The maximum depth was 31 blocks, at `k=360911` (`t=360912`);
  that tree had 43 nodes and 6 leaves.
- The empirical bound
  `depth <= 2 * bit_length(t) + 1` held for every scanned parameter.
  Equality occurred at `k=14`.

These are reproducible computational observations, not a universal
termination theorem. In particular, the scan does not replace the
formal `Closed` certificate needed by `branch29_lift`. The empirical
logarithmic depth bound is a promising next proof target because the
source-lift precision budget is linear in `k`.


## Additional #429 branch families and mixed-path structure

The manual signed-lift workflow now also compiles
[Branch13_15.lean](Branch13_15.lean). It formalizes two exact first-pair
reductions that are useful entry points for the branch-13 and branch-15
families:

- For U=24(2k+1), D=2U+18, there is no EF/SF guard at F-run lengths
  0 or 1. After exactly two F blocks the endpoint is
  (12k+6,312k+180), where SF is available, and SF outputs
  (51k+31,78k+44). At that state k=0 mod 4 is terminal,
  k=2 mod 4 admits immediate EF, and odd k admits only F.
- For U=48k+39, D=2U+18, EF is immediately available and outputs
  (60k+52,24k+28). SF is also available there; taking it gives
  (63k+58,6k+6). At that state k=1 mod 4 is terminal,
  k=3 mod 4 admits immediate EF, and even k admits only F.

The same Lean file formalizes exact endpoint defect identities for a
paired block followed by an m-block F-run. With q=2^m, pair input
(v,d), and next pair input (w,e), the identities are:

- EF: H_m(w,e)=2(w-v)+2+3m and H_m(v,d)=8q(w-v)-8.
- SF: H_m(w,e)=2(w-v)-6+3m and H_m(v,d)=8q(w-v)-20.

These are a compact arithmetic interface for mixed paths; see
[ConstantRunObstruction.md](ConstantRunObstruction.md) for the resulting
affine defect recurrence and its consequence: **no infinite signed path
can have an eventually constant even F-run length**. The proof handles
both eventually fixed pair type and eventually alternating pair type,
including the exceptional m=0 boundary cases D=0 and D=4.

**Two central ingredients are now locally Lean-certified:** [the all-denominator integer-grid packing bound](PeriodicGridPacking.lean) and [integer-affine rigidity for contracting linearly forced recurrences](AffineOrbitRigidity.lean), using Lean 4.36.0-rc2 with only standard axioms. A third locally Lean-certified module [PeriodicMacroTransfer.lean](PeriodicMacroTransfer.lean) proves that any finite typed pair/F word has exact integer-affine transfer in the source-independent half-rank model, and a repeated such word forces an exactly integer-affine first-coordinate orbit. **The remaining formal gaps** are transport from the original signed F/EF/SF blocks into this model and proof that the primitive periodic gap word yields the distinct rational rotations. Neither the original #429 machine decision nor the entire all-period no-go is Lean-certified.

The new [finite triple-repeat obstruction](FiniteTripleNoGo.md) now excludes long **finite cubes** of primitive signed pair/F words whenever (4^J>2\lfloor(r_0+2C)/3\rfloor). The exact triple-affine part is kernel-checked in [FiniteTripleRigidity.lean](FiniteTripleRigidity.lean) and [FiniteTripleMacro.lean](FiniteTripleMacro.lean); the complete primitive-rotation and original-source bridge remain paper-level. This excludes finite patterns even within aperiodic paths, though cube-free alternatives remain possible.

A new [exact signed-block bridge](SignedPairMacroBridge.lean) kernel-checks the E/S compressed macro equations and constructs the output half-rank; a [cyclic backward uniqueness theorem](ValuationPrimitive.lean) proves the finite-window rank contradiction under explicit BackwardPrimitive gap hypotheses. Both use only standard Lean axioms. The source-level periodic-path composition remains open.

The [kernel-checked exact valuation budget](ValuationPackingNoGo.md) now sharpens both no-go proofs: the new source-independent [ValuationPacking.lean](ValuationPacking.lean) and [ValuationEdges.lean](ValuationEdges.lean) prove that distinct admissible sources with 4^j*w=v+K have total j at most floor((K-1)/6). Quotient reverse-uniqueness also removes the previous fractional digit-period argument. The full source/cyclic-primitivity theorem is not yet integrated in Lean.

The stronger [all-period F-run obstruction](PeriodicRunNoGo.md) proves
at the paper level that **no infinite admissible signed path has an
eventually periodic even F-run length sequence**. This subsumes the
accepted fixed-length result above but is **not yet Lean-certified**.
Only genuinely aperiodic mixed schedules remain as infinite-path
candidates; this still does not decide a whole machine. The branch-13/15 first-pair specializations and defect
identities are CI-checked in the manual workflow (run
[45683408657](https://github.com/FlareZ123/bb6/actions/runs/45683408657),
pinned Lean 4.36.0-rc2, success on 2026-11-25). The result remains
intermediate and belongs in im-results, not results/.


## New source-rooted branch29 theorems (27 November 2026)

**Accepted:** The true blank-start #429 accelerated orbit cannot reach branch29 states with `q\bmod1024` in eight new entire residue classes; 29 more `q\bmod2048` classes are also wholly excluded. Composing with Agent18's existing sound 38/1024 necessary restriction yields the new **31/2048 necessary roster**. The three complete kernel/source checks passed: [45919337704](https://github.com/FlareZ123/bb6/actions/runs/45919337704), [45919753140](https://github.com/FlareZ123/bb6/actions/runs/45919753140), and [45919871438](https://github.com/FlareZ123/bb6/actions/runs/45919871438).

**Accepted:** The original source-connected signed-tree finite-precision theorem now excludes final-reset burst lengths `n<1,280,127` on this feeder, assuming the exact branch-7 terminal equation and `n>=18`; [CI 45920774208](https://github.com/FlareZ123/bb6/actions/runs/45920774208). This strengthens the earlier accepted `n>=16,255` floor and is a necessary bound on a particular feeder, not a machine halt decision.

**Pending:** A 31-class congruence-filtered signed certificate targets `n>=128,000,127`; no acceptance claim until its full CI source check completes.

For exact lists, source proofs, methodology, acceptance status, and research gaps, see [NEW_RESIDUE_AND_BURST_RESULTS.md](NEW_RESIDUE_AND_BURST_RESULTS.md). New reusable arbitrary-modulus shifted-affine certificate bridge: [Branch29ShiftedCert.lean](Branch29ShiftedCert.lean).
