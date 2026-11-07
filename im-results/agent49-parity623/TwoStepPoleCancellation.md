# Exact two-step pole cancellation family for #623

**Status:** exact source-level derivation; Lean source module added; CI verification pending.  
**Classification:** intermediate result and obstruction, not a blank-root reachability theorem.

## Statement

Write
\[
B_m = \operatorname{tightB}(m)=\frac{3^{m+1}-3}{2},
\qquad
x_m=3B_m+2=\frac{3^{m+2}-5}{2}.
\]
For every even m, the original Cryptids #623 high-level transition function has the exact two-step trajectory
\[
D(x_m,40x_m)
\longmapsto
D(39x_m+m+2,\;3x_m+3)
\longmapsto
D(36x_m+2m-4,\;9x_m+23).
\]
The final left gap is
\[
(36x_m+2m-4)-4(9x_m+23)=2m-96.
\]

Consequently, m=48 gives an exact zero-gap output:
\[
D(x_{48},40x_{48})
\longmapsto
D(39x_{48}+50,\;3x_{48}+3)
\longmapsto
D(4d,d),
\]
where
\[
x_{48}=358948993845926294385122,\qquad
d=3230540944613336649466121.
\]
Both transitions succeed.

## Derivation from the source evaluator and drain

The first input has even first and second counters, with x_m≤40x_m, so it uses the right-even branch. Since
\[
x_m=3B_m+2,
\]
the evaluator's first ternary digit is 2:
\[
\operatorname{evalA}(39x_m+1,x_m,2x_m+5)
=(39x_m+2,B_m,2x_m+5).
\]
The exact tight-drain identity
\[
\operatorname{drainB}(A,B_m,D)
=(A+m,D+3B_m)
\]
then gives
\[
D(39x_m+m+2,\;2x_m+5+3B_m)
=D(39x_m+m+2,\;3x_m+3).
\]

Because m and x_m are even, the new third counter 3x_m+3 is odd. The next transition is far-left odd. Its drain block count is
\[
3x_m+6=9B_m+12=B_{m+2}.
\]
Applying the same exact tight-drain identity at index m+2 gives
\[
D(36x_m+m-6+(m+2),\;5+3(3x_m+6)),
\]
which simplifies to the stated second output.

The Lean module uses Agent 8's source theorem drainB_d3_exact_iff and Agent 49's original-source #623 shift theorem. It does not replace the machine's transition function with a simulator.

## Relation to the projective pole

For the initial state D(x_m,40x_m), the parity-adjusted gaps are
\[
R=36x_m-2,\qquad L=-159x_m-5.
\]
Thus the near-then-far composite pole form is constant:
\[
53R+12L=-166.
\]
The exact two-step output gap is 2m-96. It is therefore O(m), while x_m grows exponentially in m. In particular, this family has arbitrarily large coordinates with a final gap on the logarithmic scale of the coordinate size.

This shows that the broad affine cone, the two-step projective matrix, and the parity offsets alone cannot establish a universal lower bound of order sqrt(min(a,d)), or even a universal gap lower bound larger than the logarithmic terminal window. The blank-root history is essential.

## Scope and next question

The starting states D(x_m,40x_m) are synthetic. No proof connects any member of this family to the blank-root orbit starting at D(0,7). The family therefore does not establish halting or nonhalting of the blank-root trajectory.

The useful next question is root-specific: find a history invariant that excludes the exact ratio-40 family and its logarithmic neighbourhoods from the blank-root orbit, or identify a stronger source-level restriction that distinguishes root-reachable states from these synthetic states.

## Verification record

- Lean file: [TwoStepPoleCancellationSource.lean](TwoStepPoleCancellationSource.lean)
- CI workflow: [agent49-623-ternary-shift.yml](../../.github/workflows/agent49-623-ternary-shift.yml)
- The workflow run is pending at the time this note was written. Do not cite the Lean theorem as kernel-verified until that run succeeds.
