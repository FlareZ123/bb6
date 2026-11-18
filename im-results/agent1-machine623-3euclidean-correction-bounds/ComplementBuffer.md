# Complementary affine-buffer theorem for #623

**Status:** the conditional source reduction below is an intermediate result. It does not prove nonhalting or reduce every possible root terminal state to two diagonal families. Keep in `im-results/`.

## Exact source theorem

For every positive even-first-counter state (D(a,d)) outside `newAffineCone), if its original-source transition succeeds,
[
operatorname{highLevelNext}(D(a,d))=operatorname{some}(D(b,e)),
]
then (b) is even and (2b+1\le e). If (b>0), the successor is in `newAffineCone`; (b=0) is handled by the zero-tail analysis.

This is the content of `complement_to_safe_right` in `ComplementBufferSource.lean`. It has **no exclusion hypothesis for either near-diagonal family**. The implication is conditional on success: it says where a successful transition goes, not that the current state has a successor.

## Proof outline

First, `oldAffineCone(a,d) -> newAffineCone(a,d)`. In each of the four old linear sectors, the residual ternary exponent dominates the required linear coordinate, using (u_n=(3^n-1)/2\ge n). Thus a state outside the new cone is also outside the old cone.

Split the original `highLevelNext` source branch:

- Odd (d), far-left (a\ge d+5): outside the old cone gives (a\le 2d+8); apply `far_left_odd_to_safe_right`.
- Odd (d), near-left: for (a\le d), apply `right_odd_to_safe_right), with (D(4,5)\to D(6,12)) and (D(4,7)\to D(8,12)) checked directly. For (a=d+1) or (a=d+3), apply `odd_near_diagonal_to_safe_right`.
- Even (d), far-left (a\ge d+3): outside the old cone gives (a\le 2d+4); apply `far_left_even_to_safe_right`.
- Even (d), near/right: (a\le d) is covered by `right_even_to_safe_right); (a=d+2) is covered by `even_gap_two_to_safe_right).

The conclusion (b\) even and (2b+1\le e) places every positive successful successor in the strong-right part of `newAffineCone).

## Critical limitation: this is not a two-family reduction of all root halts

The implication above is vacuous when `highLevelNext` returns `none`. It therefore cannot be used to claim that every non-boundary state outside the cone survives. In particular, `outside_old_predecessor_has_successor` and `halt_parent_in_oldAffineCone` constrain the immediate predecessor of a terminal state; they do not say that the terminal state itself must be one of the two adjacent-diagonal families.

An exact counterexample to the stronger interpretation is:
[
D(126,23)\longrightarrow D(96,91)\longrightarrow\mathrm{Halt}.
]

- (D(126,23)) is in the old affine cone: (23) is odd and (126\ge 2\cdot23+9=55).
- Its source branch is `drainB(98,26,5)). The exact evaluator steps are
  [
  \operatorname{evalA}(98,25,60)=\operatorname{some}(98,2,79),
  \]
  followed by
  [
  \operatorname{evalA}(98,1,86)=\operatorname{some}(96,0,91).
  ]
  Hence `highLevelNext(D(126,23)) = some(D(96,91))`.
- At (D(96,91)), the odd far-left branch is `drainB(0,94,5)). Its first evaluator call is
  [
  \operatorname{evalA}(0,93,196)=\operatorname{none},
  ]
  because (93\equiv0\pmod3). Thus (D(96,91)) halts.
- The terminal state is not on either narrow family: (d=91) is odd and (a=d+5), not (d+3). Its third counter also satisfies the established root-terminal lower bound (91\ge23).

This is a **synthetic** trajectory, not evidence that the blank-root orbit reaches (D(126,23)). It proves that the two narrow families are not an exhaustive set of possible terminal states, even after imposing the old-cone predecessor condition and the (d\ge23) terminal bound.

## What remains useful about the two narrow families

They are exact special reductions:
- even gap-two: (D(d+2,d)\mapsto\operatorname{drainB}(0,d+2,2));
- odd offset-three: (D(d+3,d)\mapsto\operatorname{drainB}(1,d+2,3)).

For the odd family the first evaluator is
[
\operatorname{evalA}(1,d+1,2d+10),
]
not (\operatorname{evalA}(1,d+1,d+5)). Its immediate failure condition is (d\equiv0\pmod9); a successful first evaluator does not guarantee that the residual drain succeeds. The full exact one-step fatal sets are already described by `ExactEvenSectorSource.lean`, `ExactOddSectorSource.lean`, and the finite failure-spectrum modules.

## Correct root-level target

The genuine blank-root problem remains to exclude **all** terminal outputs from old-cone predecessors, across the four source sectors. The source-certified logarithmic terminal windows in `TerminalRatio4Source.lean` and the canonical-ray distance identities in `CanonicalRayRootDistanceArithmetic.lean` remain relevant. A root-specific all-time invariant must keep the actual (D(0,7)) orbit outside every such window, or produce a genuine halt witness. The two boundary digit-stack problems are useful subproblems, not a complete replacement for that obligation.
