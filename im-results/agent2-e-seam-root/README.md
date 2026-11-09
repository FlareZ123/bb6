# D Cryptid: source-certified all-suffix F-section first-event law

**Status: fully Lean-kernel verified, 9 November 2026, intermediate prepared-tape theorem.** It does not decide the blank orbit of machine D or BB(6).

The actual original six-state, two-symbol machine is
`1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`.
Write `I_n(s)` for a physically blank-left F/0 section with a right tape
consisting of `n` consecutive ones, then `s`, then implicit zeros.
For every finite binary right suffix `Y`, define

`F_k(Y) = I_(3k+4)(0Y)`, `P(k)=12k²+41k+33`.

## Certified theorem

[FullFFirstEvent.lean](FullFFirstEvent.lean), theorem
`BB6.Agent2ESeamFRoot.all_prepared_F_first_events`, establishes the
following **exhaustive all-parameter dichotomy** for each finite `Y`:

1. **Return case.** There exists a common natural `t=t(Y)` such that every
   `k≥0` first returns to a *physically blank-left* F/0 section after
   precisely `P(k)+t+8k+2=12k²+49k+35+t` primitive transitions.
   At every strictly positive earlier time, neither physical F/0 return
   nor F/1 halt gate occurs.
2. **No-return case.** For every `k` and every positive primitive time,
   there is no physically blank-left F/0 return. At each
   `j≥P(k)`, the F/1 halt gate of the original F-section run at time
   `j` is **equivalent** to the F/1 halt gate of the common E3 core at
   time `j-P(k)`. There are no F visits during the initial
   `0<j<P(k)` delimiter prefix.

The independent corollary
[ReturnEquivalence.lean](ReturnEquivalence.lean),
`positive_F_return_iff`, proves for every `k,h,Y`:

```text
(∃ j>0, physicalReturn(run j F_k(Y)))
  ↔ (∃ j>0, physicalReturn(run j F_h(Y))).
```

The positive-time qualification excludes the trivial starting F/0 event.
No finite cutoff, tail-length restriction, or conjectured halting behavior
enters either theorem.

## Proof and integration

The proof composes the complete all-time,
original-source E3 marker certificate of Agent 25
[`SourceSeamComplete.source_e_all_m_first_event`](../agent25-e-seam-kernel/README.md)
with the original `CryptidBoundary.prefix_E` transition identity and
Agent 2's existing `prefixE_positive_noF`. The prefix lands **exactly**
at `eSector (4*k) Y` after `P(k)` steps. The E-sector return delay
`2*(4k)+2` yields the quadratic return time; its no-return branch
gives the exact unbounded F/1 predicate transfer. An explicit equality of
run configurations avoids accidentally rewriting the arithmetic time
index inside the *target* halt comparison.

The unchanged six-state source, all 6,399 finite-certificate states,
physical-window-to-source refinement, F delimiter theorem, and the two
new files are reconstructed and checked by
[manual workflow](../../.github/workflows/agent2-e-seam-first-event.yml).
**[CI run 42577258138 succeeded](https://github.com/FlareZ123/bb6/actions/runs/42577258138)**
with Lean 4.36.0-rc2, with the concluding proof audit showing
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` or
`native_decide`. The first compile attempt timed out on an unnecessary
bidirectional time-index elaboration; the corrected proof is the one
in this passing run.

The mathematical first-event shift for E inputs was already proposed
in Agent 31's E-cocycle analysis; the contribution here is a single
source-connected theorem about *all prepared original F sections* with
strict first-event semantics, and its uniform return-existence corollary.
No claim of external originality or a BB(6) bound is made.

## Outstanding mathematical target

Apply this source-level all-suffix theorem to a **source-certified authentic
blank-root E entry**, then classify the actual reachable right-suffix
language through the A/B/exceptional E descendants. The parameter
independence removes unary-prefix size from that classification but
does not determine which suffixes are genuinely blank-reachable.
