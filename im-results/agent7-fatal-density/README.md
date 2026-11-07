# Cryptids #746: source-certified six-packet inverse grammar and 3-adic fork constraints

**Research state (6 November 2026): original-source all-index arithmetic and six-packet root reductions constrain hypothetical #746 fatal ancestors; blank-start halting and BB(6) remain open.** [Complete proof derivations, density analysis, and historical chronology](FULL_RESEARCH_LOG.md).

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


## Second-parent dyadic-gap reduction

[TThreeHighTightBounds.lean](TThreeHighTightBounds.lean) formalizes a further geometric consequence of the exact high-q margin. Put (p=2^{n-4}), (k=n-6), and let (r) be the second (t=3) parent. The source equations and margin imply
[
10934p-961n+18609\le6561r\le10942p-10177n+6321.
]
They consequently force
[
4\cdot2^k<\frac{2r+5}{3}<6\cdot2^k,
\qquad
2\cdot2^k<\frac{2(2r+5)}{9}<3\cdot2^k,
]
whenever the respective quotients are integral.

These are strict dyadic gaps: the first lies between the odd-parent bands at scales (k-1) and (k), and the second lies between the bands at scales (k-2) and (k-1). Therefore an odd parent of (r), if one exists, cannot have exponent (t=0) or (t=1); every possible odd parent has (t\ge2). This is a root-cone reduction beyond the residue selector.

The Lean file proves the arithmetic implication from Int-cast source equations and margin hypotheses, plus the scaled gap inequalities. Full unchanged-source Lean CI passed in [42407885455](https://github.com/FlareZ123/bb6/actions/runs/42407885455); the Nat-to-Int margin bridge and direct composition with the complete reset-parent grammar remain to be checked. Do not yet claim that the second-parent branch is root-dead.

## Remaining question

The resulting fork recursion retains source-possible branches, including higher 3-adic valuations. No uniform proof separates **all** surviving fatal gates from the genuine `C(2,0)` root, and no original raw-machine halt has been produced. Find a full symbolic odd-fork closure or a genuine root witness; avoid interpreting formal inverse densities as a true trajectory frequency.

See [FULL_RESEARCH_LOG.md](FULL_RESEARCH_LOG.md) for the exact Hensel residue recurrences, packet inequalities, paper extensions, evidence scopes and counterexamples.
