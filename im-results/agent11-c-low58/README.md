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

The fast leaf was compiled locally with Lean 4.36.0-rc2. Its axiom audit reports only `propext` and `Quot.sound`; no `sorryAx`. It has been wired into `ValSixC58AllDepthBool.lean` and the existing manual source workflow, but this newest integration is **not yet source-CI certified**. The latest full workflow run, [42374537334](https://github.com/FlareZ123/bb6/actions/runs/42374537334), failed in the separate Agent19 `HighThreeLate256.lean` leaf (a type mismatch and heartbeat timeouts). That failure does not falsify the fast-gate proof; it blocks a clean full-workflow acceptance run. Do not describe the fast gate as source-certified until the complete workflow passes.

## Formal artifacts and verification boundary

| Artifact | Claim | Verification |
| --- | --- | --- |
| `Low58Source.lean` | low `m%256=150` exclusion | source CI 42280559453, success |
| `Low14Source.lean` | low `m%64=58` exclusion | source CI 42282006382, success |
| `Rect58Source.lean` | full two-dimensional rectangle and high family | source CI 42283365249, success |
| `ValSixC58AllDepth.lean` | exact C58/ValSix criterion plus all-depth cone | source CI 42335683875, success |
| `HighDyadicGateDecision.lean` and `HighDyadicDepthUnique.lean` | exact bounded Boolean scan and at-most-one-depth lemma | source CI 42336297638, success |
| `HighDyadicGateDecisionFast.lean` | direct valuation candidate and equivalence to the scan | local Lean 4.36.0-rc2 only; full source CI pending |

All cited source theorems have standard Lean axiom audits without `sorryAx`. The M512 counts are finite computational evidence, not a proof of actual reachability.

## Remaining mathematical obstacle

The integrated theorem is an exact reformulation and restriction of Machine C's blank-start halting condition. It does not prove that the remaining low or high existential branches are empty, and it does not produce a reachable halting target. The next decisive task is a root-sensitive proof: either find a genuine blank-root witness accepted by the exact stopping criterion, or prove that every remaining parameter pair fails the fixed-target root decision. Agent 4's fixed-target root-probe work is complementary; avoid duplicating its runtime measurements.

All material here remains in `im-results/`. Promotion to `results/` requires independent novelty review and a theorem-level contribution that is suitable for academic publication.
