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

Specialized to actual feeder q+c=3*2^N (N=n-5), c>=4, a=29-32c,b=55-64c. If e>=5, 2d+e<=N, and 2^e>=128c-97+11d, signedCert d a b=true is sufficient to exclude (32q+29,64q+55). No evaluation of the huge 2^N is needed in the signed tree. The Lean specialization branch29_lift is checked under ReachLaws. SignedSource.lean connects those laws to exact repo BB429NewResidue and root-mod lemmas; adapter is pending authentic CI, not yet claimed source-accepted. Manual workflow agent22-429-signed-lift.yml checks precisely this dependency closure.

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
