# Cryptids #746: source-certified six-packet inverse grammar and 3-adic fork constraints

**Research state (7 November 2026): original-source all-index arithmetic and six-packet root reductions constrain hypothetical #746 fatal ancestors; blank-start halting and BB(6) remain open.** [Complete proof derivations, density analysis, and historical chronology](FULL_RESEARCH_LOG.md).

## Source-certified result

For each surviving fatal-index sector `n%6∈{4,5}`, [FatalHenselResidue.lean](FatalHenselResidue.lean) gives exact 3-adic residue conditions for divisibility of the formal fatal-gate numerator. This describes hypothetical inverse opportunities; it does not supply actual blank-root reachability or a frequency of genuine orbit events.

Newer [RayResidues.lean](RayResidues.lean), [RayNonFork.lean](RayNonFork.lean), [SixPacketRoot.lean](SixPacketRoot.lean), [ForkDecompose.lean](ForkDecompose.lean), [PacketSelector.lean](PacketSelector.lean), [FatalPacket.lean](FatalPacket.lean), [RayForkPrune.lean](RayForkPrune.lean), and [OddCandidate.lean](OddCandidate.lean) establish the **exact 0/3/6 modulo-9 permutation** at even depth, five unique nonfork first-reset source parents per complete high-band six-packet, and a lossless rooted criterion reducing each packet to its depth-six continuation or the remaining genuine odd-fork ancestors. For surviving fatal `n≥10`, source-certified conditional divisibility tests prune some odd arms. Successful unchanged-source CI runs include [42132557789](https://github.com/FlareZ123/bb6/actions/runs/42132557789), [42133134677](https://github.com/FlareZ123/bb6/actions/runs/42133134677), [42133586305](https://github.com/FlareZ123/bb6/actions/runs/42133586305), [42134663672](https://github.com/FlareZ123/bb6/actions/runs/42134663672), and [42135230195](https://github.com/FlareZ123/bb6/actions/runs/42135230195).

The earlier source-certified [SignedRayPeriod.lean](SignedRayPeriod.lean) six-step modulo-nine theorem is a component, with successful [CI 42124540499](https://github.com/FlareZ123/bb6/actions/runs/42124540499). Formal signed inverse-ray densities are mathematical statements about the parameter space. A locally checked modulo-27 `RayTriplePeriod` draft has separate source-verification status; it is not part of the above certified six-packet result.


## Translated high-q gate and second-parent selector

[TranslatedDepthResidue.lean](TranslatedDepthResidue.lean) extends the inverse-ray Hensel tower from the zero target to every integer offset divisible by (81). For each precision (3^{k+4}), it proves exactly one index class modulo (2\cdot3^{k+3}). Its source-gate specialization proves that the (t=3) high-(q) condition (81\mid(2q+5)), under the exact source equations, is equivalent to one residue class modulo (4374).

A further precision-nine lift identifies the second (t=3) parent branch:
[
r\equiv0\pmod3
\iff
3^9\mid Z_j(n)-A_{0,n},
\qquad
j\equiv R_{0}(n)\pmod{13122}.
]
This is exactly the (r\bmod3=0) case covered by Agent 10's existing root-dead theorem. The (r\bmod3=1,2) branches remain open. The translated tower and exact source-gate bridge passed full-source Lean CI in [42403440784](https://github.com/FlareZ123/bb6/actions/runs/42403440784) and [42404035998](https://github.com/FlareZ123/bb6/actions/runs/42404035998); the precision-nine second-parent theorem passed in [42404919018](https://github.com/FlareZ123/bb6/actions/runs/42404919018). All new theorem audits have only standard Lean logical axioms.

[ForwardOrbitAudit100k.md](ForwardOrbitAudit100k.md) records an independent exact-integer finite check: 245,399 high-(q) candidates for (20\le n\le100000) were compared with the deterministic blank-root reset orbit, with zero matches. This extends finite evidence; it is not a universal exclusion theorem. The executable audit is [t3_high_gate_forward_audit.py](t3_high_gate_forward_audit.py).


## Source-connected high-q second-parent inverse grammar

Fix a canonical ray index \(n\ge20\), \(n\bmod6\in\{4,5\}\), depth \(j\), and exact source high-margin \(2048D_j(n)+16384n+16384\le 2^n\). Assume the actual source reset equations
\[
2U_j(n)+5=81d_0,\quad16d_0=2^n+q+(n-3)+5,\quad
2q+5=81e,\quad16e=8\cdot2^{n-6}+r+(n-6)+5.
\]
The previous [TThreeHighTightBounds.lean](TThreeHighTightBounds.lean) algebra, new [TThreeHighNatBridge.lean](TThreeHighNatBridge.lean), and [TThreeHighNatSource.lean](TThreeHighNatSource.lean) jointly prove the source-level bounds
\[
10934p-961n+18609\le6561r\le10942p-10177n+6321,\qquad p=2^{n-4}.
\]
This completes the missing Nat-to-Int margin bridge. [TThreeHighOddPrune.lean](TThreeHighOddPrune.lean) uses the *complete* actual first-reset predecessor grammar to exclude odd valuations \(t=0,1\) at \(r\). Original-source Lean CI [42410401513](https://github.com/FlareZ123/bb6/actions/runs/42410401513) passed.

### Uniform genuine-root obstruction at \(t=2\)

Any odd valuation-\(2\) predecessor \(a\) of \(r\) has quotient \(d\), with \(2r+5=27d\). [TThreeHighTTwoGeometry.lean](TThreeHighTTwoGeometry.lean) proves its dyadic scale is uniquely \(k=n-8\), putting \(s=2^{n-8}\) and \(1973s\le1000d\le1979s\). Four successive candidate even predecessors \(b,c,f,g\) satisfy
\[
8d=8s+a+k+5,\quad2a=8s+b+k,\quad
2b=8s+c+k,\quad2c=8s+f+k,\quad2f=8s+g+k.
\]
All of \(a,b,c,f\) are in the exact source even-return band of scale \(k\), while \(g\) lies in a strict gap \(4s<g\) and \(2g+2<12s\). If \(d\bmod3=2\), all five are residue \(1\) modulo 3; the first four predecessors are therefore forced even, and source-root reachability contradicts the forbidden gap at \(g\). [TThreeHighTTwoRoot.lean](TThreeHighTTwoRoot.lean) proves this at arbitrary exact odd-image exponent and integrates it into an all-source ResetParent classifier. Full source Lean CI [42411744664](https://github.com/FlareZ123/bb6/actions/runs/42411744664) **passed**, with no extra axioms beyond ordinary Lean logic.

For \(d\bmod3=0\), [TThreeHighTTwoZero.lean](TThreeHighTTwoZero.lean) establishes the stronger rooted condition \((2b+5)\bmod9=0\) **or** \((2f+5)\bmod27=0\). Thus **all** quotients \(d\bmod9=0\) are excluded. The necessary quotient classification becomes
\[
d\bmod9=6\quad\lor\quad
(128d)\bmod27=(30(8\cdot2^{n-8}+n-8)+75)\bmod27.
\]
[TThreeHighTTwoResidues.lean](TThreeHighTTwoResidues.lean) classifies the second case by \(n\bmod18\): indices \(4,17\) require \(d\bmod27=12\); indices \(5,10\) require \(d\bmod27=21\); indices \(11,16\) require \(d\bmod27=3\). Both the quotient-zero and indexed period-18 residue proofs passed complete, unchanged-source Lean 4.36.0-rc2 CI [42413863136](https://github.com/FlareZ123/bb6/actions/runs/42413863136). The audited theorems depend only on standard logical axioms (propext, Classical.choice, Quot.sound), without source stubs or sorry. [TThreeHighTTwoFinalSelector.lean](TThreeHighTTwoFinalSelector.lean) packages these cases together with the d%3=2 exclusion as one universal *necessary* rooted 13-of-27 quotient-residue selector for every exact t=2 source arm. Its complete original-source Lean CI [42414216925](https://github.com/FlareZ123/bb6/actions/runs/42414216925) **PASSED** with no source stubs or sorry. Consequently 14 of 27 formal quotient residue classes are genuinely root-excluded in every surviving n%18 sector; the remaining 13 classes are not proved root-reachable.

The \(d\bmod3=1\) branch, surviving modulo-27 gates, valuations \(t\ge3\), other \(q\)-selector arms, and the continuing inverse ray remain open. The source-root restrictions do not establish that machine #746 halts or never halts. They are neither a BB(6) upper bound nor an exact BB(6) value.

## Remaining question

The resulting fork recursion retains source-possible branches, including higher 3-adic valuations. No uniform proof separates **all** surviving fatal gates from the genuine `C(2,0)` root, and no original raw-machine halt has been produced. Find a full symbolic odd-fork closure or a genuine root witness; avoid interpreting formal inverse densities as a true trajectory frequency.

See [FULL_RESEARCH_LOG.md](FULL_RESEARCH_LOG.md) for the exact Hensel residue recurrences, packet inequalities, paper extensions, evidence scopes and counterexamples.


## Quotient d = 1 mod 3: forced odd continuation

The new TThreeHighTTwoOne.lean and TThreeHighTTwoOneArithmetic.lean cover the previously open d%3=1 t=2 branch at the source-root level. The four-even residues are (a,b,c,f,g)=(2,0,2,0,2) mod 3. If neither 9|(2a+5) nor 9|(2c+5), root reachability forces the fourth even ancestor g to be rooted. The existing strict even-image gap at g then forces an actual odd source predecessor there, recorded by GapOddParent.

The exact necessary selector is: for n%18 in {4,17}, d%9 is 1 or 4 or GapOddParent(g); for n%18 in {5,10}, d%9 is 4 or 7 or GapOddParent(g); for n%18 in {11,16}, d%9 is 1 or 7 or GapOddParent(g). The third residue in each sector is routed into the odd fork. It is not root-excluded. The result is an intermediate necessary-condition refinement and does not close the d%3=1 branch.

Full-source Lean 4.36.0-rc2 CI passed on branch commit 78ecb666ef4071a0f24c86200466a99d770320c2: [run 42433786158](https://github.com/FlareZ123/bb6/actions/runs/42433786158). The check compiled the actual imported source modules, with no source stubs.


## Independent high-level acceleration for #746

The same machine is formalized independently in Google DeepMind's Cryptids repository. Its machine-specific Lean module defines a high-level C(a,b) map with start C(0,2), whose first transition reaches the local source root C(2,0). The map has the exact cases:
- C(a,0) -> C(2,2a+1);
- C(a,1) -> halt;
- for b>=2, put d=b-2; if d>=2a then C(2a+2,d-2a);
- otherwise use the odd/even modulo-four branches with numerators 6a+d+5 or 6a+d+8.

The local ResetParent even/odd equations line up algebraically with the C-to-C cascade in this accelerated map. In the odd branch, the intermediate shifted coordinate c=2^t z undergoes the finite underflow c -> 3c/2 while it remains even, followed by a final transition with 2g+5=3^(t+1)z. This is the same 3/2 structure exposed by GapOddParent(g). A formal edge-by-edge refinement between the two independent Lean developments remains a high-value next task.

The external Hardness note reports 1,253 cascades and an estimated hazard around 10^-294. Treat that hazard as a heuristic, not as a proof of non-halting. See resources/cryptids-bb6-2026.md for source links, the exact map, and the derived drain equations.


## Formal high-level odd-underflow tail

The independent C(a,b) map is transcribed in HighLevel746Underflow.lean. Lean proves that when a C(y,2) state has shifted coordinate c=y+3 even, the next transition sends c to 3c/2 while the second coordinate remains 2. For c=2^t z with z odd, t such transitions reach c=3^t z, which is odd; the final transition returns to C(g,0) with 2g+5=3^(t+1)z.

TThreeHighTTwoOneHighLevel.lean packages this as a theorem from GapOddParent(g): the exact odd source witness supplies a finite high-level underflow path from C(2^t z-3,2) to C(g,0), while preserving the root-reachable x and the source scale equation 2*(2^t z)=8*2^l+x+l+5. The l-step high-b drain from C(x,0) to the intermediate C-state is not yet part of this bridge.

The new modules are committed on branch agent7-highlevel-underflow; targeted full-source CI is pending.
