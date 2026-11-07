# Machine C: source-authentic C58 rectangle and all-depth stopping criterion

**Status, 7 November 2026: Machine C and BB(6) remain unresolved.** The source-authentic C58/ValSix criterion now combines the exact C58 exclusions, the complete ValSixFull restrictions, and an unbounded dyadic inverse-depth high exclusion. Its fixed-target root decisions are exact, but the existential stopping parameters remain unbounded. No complete halt/nonhalt decision follows.

## Exact source-level C58 exclusions

Let `CReach x y` be eventual section reachability from the authentic blank-derived seed `(5,1)`, using the original Machine C section transition `secNext`.

### Infinite low and high families

- `Low58Source.lean` proves `blank_no_low_m_150`: every low stopping index `m % 256 = 150` is unreachable.
- `Low14Source.lean` proves that every target `(1,64*t+14)` is unreachable. This removes all low indices `m % 64 = 58`, including its base case.
- `Rect58Source.lean` proves the full infinite rectangle
  ```lean
  theorem blank_no_rect_58_full (x y : Nat)
      (hx : x%64=1) (hy : y%256=58) :
      ¬ BB6.Agent3.CReach x y
  ```
  and hence removes every high stopping pair satisfying
  `m ≥ 3`, `j % 32 = 31`, and `(j+3*m+5) % 256 = 198`.

The rectangle proof is uniform in both parameters. It has no time bound, predecessor-depth cutoff, or periodicity assumption. Write the forbidden target as `T=(64u+1,256v+58)`. Two forced direct predecessors are
```text
R1 = (64u+256v+57, 128v+28)
R2 = (64u+384v+83,  64v+13).
```
The complete original-source inverse of `R2` admits only
```text
A = (32u+224v+46, 16u+144v+28)
B = ( 8u+ 56v+10, 28u+228v+43).
```
The sum of the coordinates of `R2` has 2-adic valuation exactly five, so only even-bounce depths zero and two are possible. The exact inverse of `A` is forced to `C=(48u+368v+72, 8u+72v+13)`. Both `B` and `C` have odd right counter and coordinate sum congruent to one modulo four, contradicting the genuine blank-orbit odd-image invariant. The complete inverse grammar also rules out the odd-source and exceptional zero/one-left branches. The time-zero state is handled separately.

The proof imports the complete source relation `section_preimage_all_iff` and the exact even-right equivalence. It is a genuine blank-root nonreachability result for this section, not a quotient-only argument.

### Comparison with the finite M512 quotient

The independent M512 quotient census has 27,858,704 reached abstract states and 221,572,376 generated candidate edges. All 16 cells in the C58 rectangle, with `x∈{1,65,129,193,257,321,385,449}` and `y∈{58,314}`, are admitted by that finite quotient. This is a computational observation about that abstraction. The Lean source theorem proves the entire rectangle unreachable in the original section. The low-14 family, by contrast, was already rejected by the tested M512 quotient.

## Integrated all-depth Machine C criterion

The key integration is `ValSixC58AllDepth.lean`, with the exact theorem
`BB6.Agent11C58AllDepth.blank_halts_iff_joint_c58_all_depth`.

It preserves the exact low stopping branch and combines the previous Agent3/11/19/29 ValSixFull+C58 high restrictions with Agent19's source-certified all-depth dyadic cone. The high predicate is the previous exact `BB6.Agent11C58ValSix.highAllowed` predicate together with
```text
∀ r,
  ¬(2≤r ∧ 3≤m ∧ r+4≤2*m+2 ∧
    m%4=(2*r+3)%4 ∧
    (j+9*m+14)%2^(r+4)=3*2^(r+2)).
```
The final high stopping target remains
`(2*j+3, 2^(2*m+2)*(j+3)-(j+3*m+5))`.
The root evaluator `BB6.Agent3ValSix.valSixMixedRootDecision` is exact for each fixed target. The existential quantifiers over `m` and `(j,m)` are still unbounded.

The all-depth cone itself is source-certified in [CI 42334843728](https://github.com/FlareZ123/bb6/actions/runs/42334843728). The complete C58/ValSix all-depth integration, including its independent-family checks, passed original-source CI [42335683875](https://github.com/FlareZ123/bb6/actions/runs/42335683875). The bounded executable scan and unique-depth theorem were included in successful manual source CI [42336297638](https://github.com/FlareZ123/bb6/actions/runs/42336297638). These runs use Lean 4.36.0-rc2 and the original source dependency chain.

### Strictly new infinite exclusions beyond the previous combined sieve

The source-checked integration proves three explicit independence results:

1. At depth two, every `(j,m)=(7+64t,3)` passes the previous combined C58/ValSix predicate and is excluded by the new dyadic gate.
2. At depth three, every `(j,m)=(37+128t,5)` passes the previous combined predicate and is excluded by the new gate.
3. For every `t`, put `r=130+128t`, `m=2r-1`, and `j=3*2^(r+2)-(18r+5)`. The previous combined predicate admits this pair, while the arbitrary-depth source cone excludes it. The theorem also proves that distinct `t` give distinct `m`, so this is an infinite family of genuinely distinct exclusions.

These are parameter exclusions for Machine C's exact stopping criterion. They do not establish that the remaining parameter sets are empty.

## Direct one-depth evaluator

The previous executable gate, `HighDyadicGateDecision.lean`, tests every `r` in `List.range (2*m+1)`. The range is exact because the gate itself requires `r+4≤2*m+2`.

A sharper identity removes this linear scan. For
`D=j+9*m+14`, the residue equation gives
```text
D % 2^(r+4) = 3*2^(r+2)
    ⇒ D = 2^(r+2) * (4*q+3)
    ⇒ v2(D) = r+2.
```
Therefore any qualifying depth is unique and is exactly `v2(D)-2`. The new `HighDyadicGateDecisionFast.lean` defines a logarithmic-time recursive `v2` evaluator and a Boolean that checks only this candidate. Its theorems are:

- `v2_of_high_residue`: the residue equation determines the exact 2-adic valuation.
- `candidateAllowedBool_iff`: the one-candidate Boolean is equivalent to exclusion at every depth.
- `candidate_matches_scan`: the new Boolean is extensionally identical to the previous bounded scan.

The fast leaf was compiled locally with Lean 4.36.0-rc2. Its axiom audit reports only `propext` and `Quot.sound`; no `sorryAx`. It is wired into `ValSixC58AllDepthBool.lean` and the manual source workflow. Full source verification is still pending: run [42394679706](https://github.com/FlareZ123/bb6/actions/runs/42394679706) compiled all three valuation leaves and the C58 Boolean criterion, then stopped at `ValSixC58Late.lean:90` because the strict-family proof still used the old Boolean name. I repaired that bridge with `candidate_matches_scan`; run 17 ([42395358939](https://github.com/FlareZ123/bb6/actions/runs/42395358939)) is queued with the fix and the additional leaves. The earlier `HighThreeLate256.lean` heartbeat/type issues have also received isolated proof-structure repairs, but the new full chain has not yet passed. Do not describe these additions as source-CI certified until run 17 completes successfully.

## Direct evaluator for Agent19's older all-depth guard

Agent19's older high guard contains the residue
```text
(j+3*m+3) % 2^(n+4) = 2^(n+2).
```
Writing `D=j+3*m+3` and `q=D/2^(n+4)` gives
```text
D = 2^(n+2)*(4*q+1)
  ⇒ v2(D)=n+2.
```
Thus the only possible depth is `n=v2(j+3*m+3)-2`. The new
`HighDyadicOlderGateFast.lean` checks this candidate, the original
upper bound `n+4≤2*m+2`, and the parity-dependent right-coordinate
condition. Its `candidateAllowedBool_iff` proves exact equivalence to
`∀ n, ¬gate n j m`, and `candidateAllowedDecidable` supplies a named
computable decision procedure. This is designed to replace the
`List.range (2*m+1)` scan in Agent27's `FullBoolean.lean` without
changing the mathematical predicate. It locally compiles with Lean
4.36.0-rc2 and no `sorryAx`; run 17 is the first source-workflow check.

The companion `OlderGateRawRootExamples.lean` formally certifies depth-`n=0`
witnesses for high target pairs `(j,m)=(14,1),(30,1),(46,1)`, so the
direct Boolean rejects those three members of Agent4's 326-point
raw-mass-2000 box. This is a concrete finite filter evaluation; it does
not establish that these are the only older-gate exclusions in the box.

## Formal artifacts and verification boundary

| Artifact | Claim | Verification |
| --- | --- | --- |
| `Low58Source.lean` | low `m%256=150` exclusion | source CI 42280559453, success |
| `Low14Source.lean` | low `m%64=58` exclusion | source CI 42282006382, success |
| `Rect58Source.lean` | full two-dimensional rectangle and high family | source CI 42283365249, success |
| `ValSixC58AllDepth.lean` | exact C58/ValSix criterion plus all-depth cone | source CI 42335683875, success |
| `HighDyadicGateDecision.lean` and `HighDyadicDepthUnique.lean` | exact bounded Boolean scan and at-most-one-depth lemma | source CI 42336297638, success |
| `HighDyadicGateDecisionFast.lean` | direct valuation candidate and equivalence to the scan | local Lean 4.36.0-rc2 only; full source CI pending |
| `HighDyadicOlderGateFast.lean` | direct candidate for Agent19's parity-dependent older depth guard | local Lean 4.36.0-rc2 only; run 17 pending |
| `HighThreeLateGateFast.lean` | direct candidate for the arbitrary-depth late three-cone | local Lean 4.36.0-rc2 only; run 17 pending |
| `ValSixC58LateFast.lean` | exact C58 criterion strengthened by the late cone | locally typechecked against interface stubs; run 17 pending |

All cited source theorems have standard Lean axiom audits without `sorryAx`. The M512 counts are finite computational evidence, not a proof of actual reachability.

## Arbitrary-depth late three-cone gate

Agent19's separate `HighThreeLate.lean` exclusion uses the residue
```text
(k+2) % 2^(r+2) = 3*2^r
```
together with `r≥2`, `m≥3`, `m%4=(2*r+1)%4`, and
`7*2^r≤k+2`, where
```text
k = 2^(2*m+2)*(j+3) - (j+3*m+5).
```
There is no upper bound on `r`. The same factorization gives
```text
k+2 = 2^r*(4*q+3)
    ⇒ v2(k+2)=r.
```
The new `HighThreeLateGateFast.lean` therefore checks only the candidate
`r=v2(k+2)`. Its `candidateAllowedBool_iff` proves that the Boolean is
true exactly when some arbitrary depth satisfies the full three-cone
hypotheses; `allowedBool_iff` proves that its negation is equivalent to
exclusion at every depth. This is independent of the older gate based on
`j+9*m+14`, and it has no stopping-exponent cutoff.

`ValSixC58LateFast.lean` wraps the source theorem
`BB6.Agent11HighThreeLate.late_high_no_blank` into a stronger exact
blank-halting iff, adding this all-depth late-cone filter to the previous
C58/ValSix high predicate. It also retains the old-sieve-admitted family
`m=3, j=372+512*t` as a strictness witness. The arithmetic leaf compiles
locally with Lean 4.36.0-rc2 and its axiom audit has no `sorryAx`; the
wrapper has been typechecked locally against matching interface stubs.
Neither file has yet passed the complete original-source CI chain. The
existing full workflow is still blocked by the separate
`HighThreeLate256.lean` experiment, whose latest run is
[42374537334](https://github.com/FlareZ123/bb6/actions/runs/42374537334).
The failure includes a missing `dsimp [j]` in an old-sieve admission
obligation, an affine-normalizer argument type mismatch, and expensive
Omega/definitional-reduction steps. The exact status of that experiment
must remain separate from the already established general
`late_high_no_blank` source theorem and from these locally checked
valuation lemmas.

## Remaining mathematical obstacle

The integrated theorem is an exact reformulation and restriction of Machine C's blank-start halting condition. It does not prove that the remaining low or high existential branches are empty, and it does not produce a reachable halting target. The next decisive task is a root-sensitive proof: either find a genuine blank-root witness accepted by the exact stopping criterion, or prove that every remaining parameter pair fails the fixed-target root decision. Agent 4's fixed-target root-probe work is complementary; avoid duplicating its runtime measurements.

All material here remains in `im-results/`. Promotion to `results/` requires independent novelty review and a theorem-level contribution that is suitable for academic publication.
