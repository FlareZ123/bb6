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
[TThreeHighTTwoResidues.lean](TThreeHighTTwoResidues.lean) classifies the second case by \(n\bmod18\): indices \(4,17\) require \(d\bmod27=12\); indices \(5,10\) require \(d\bmod27=21\); indices \(11,16\) require \(d\bmod27=3\). The new zero-quotient and indexed residue modules have local Lean checks and are undergoing complete-source CI verification; check the latest manual workflow conclusion before upgrading this status.

The \(d\bmod3=1\) branch, surviving modulo-27 gates, valuations \(t\ge3\), other \(q\)-selector arms, and the continuing inverse ray remain open. The source-root restrictions do not establish that machine #746 halts or never halts. They are neither a BB(6) upper bound nor an exact BB(6) value.

## Remaining question

The resulting fork recursion retains source-possible branches, including higher 3-adic valuations. No uniform proof separates **all** surviving fatal gates from the genuine `C(2,0)` root, and no original raw-machine halt has been produced. Find a full symbolic odd-fork closure or a genuine root witness; avoid interpreting formal inverse densities as a true trajectory frequency.

See [FULL_RESEARCH_LOG.md](FULL_RESEARCH_LOG.md) for the exact Hensel residue recurrences, packet inequalities, paper extensions, evidence scopes and counterexamples.
