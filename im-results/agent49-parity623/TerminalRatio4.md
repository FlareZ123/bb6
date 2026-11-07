# Terminal ratio-4 separation from the root-ray bridge

**Agent 49, 2026-11-07. Algebraic synthesis; four-sector source formalization and finite audit passed pinned CI.**

This combines the root-ray bridge with the joint-mass drain bound. It gives a
single necessary condition on the predecessor coordinates if a B-drain output
is terminal.

## Output balance

Suppose a drain produces D(a',d') and highLevelNext(D(a',d')) is none.
The no-successor power-gap lemma gives

[
3^{d'-a'-5}le 2(a'+d')+5,qquad
3^{a'-d'-5}le 2(a'+d')+5.
]

If a joint-mass envelope M satisfies a'+d'≤M and
2M+5<3^K, monotonicity of powers of 3 gives

[
|d'-a'|le K+4.
]

## Cancellation of output coordinates

Set

[
G_R=d'-4a'-c_R,qquad G_L=a'-4d'-c_L,
]

where c_R∈{1,2} and c_L∈{5,9}. Then

[
G_R-G_L=5(d'-a')+(c_L-c_R).
]

The root-ray bridge bounds G_R and G_L around predecessor forms. Their
difference cancels the output coordinates:

- far-left: (7y-4x)-(x-13y)=5(4y-x);
- near-left: (7x-4y)-(y-13x)=5(4x-y).

Since |c_L-c_R|≤8 and |d'-a'|≤K+4, adding the two bridge errors yields:

| Branch | Error sum | Joint-mass envelope M | Necessary condition |
|---|---:|---|---|
| odd far-left | 25n+118 | x+2y+10+3n | |4y-x|≤K+5n+29 |
| even far-left | 25n+73 | x+2y+7+3n | |4y-x|≤K+5n+20 |
| odd near-left | 25n+32 | y+2x+5+3n | |4x-y|≤K+5n+12 |
| even near-left | 40n+58 | y+2x+5+3n | |4x-y|≤K+8n+17 |

In each row, K is the least integer such that 2M+5<3^K. For even
near-left, the mass envelope y+2x+5+3n is obtained by composing the
positive/zero evaluator lemmas with the joint-mass drain theorem.

The integer bounds above use the fact that the left-hand side is integral.
Before rounding, the inequalities are respectively
5|4y-x|≤5K+25n+146,
5|4y-x|≤5K+25n+101,
5|4x-y|≤5K+25n+60, and
5|4x-y|≤5K+40n+86.

## Finite blank-root scan

The first 10,000 states give 9,991 final-drain inputs. Only one state meets
the combined necessary ratio-4 condition: index 13, right-even D(122,438),
with |4x-y|=50 and bound 64. Its drain output is D(314,385), which has
successor D(74,950), so it is not terminal.

Index 16, far-left-odd D(876,235), has gap 64 and bound 62, so it is
excluded. There are no further candidates in the scanned prefix.

From index 17 onward, the minimum margins by branch are:
- right-odd: 1,196 at index 21;
- right-even: 674 at index 23;
- far-left-odd: 425 at index 19;
- far-left-even: 2,838 at index 22.

These are finite observations, not an all-time orbit proof. The generic
output-balance lemma and four branch-specific ratio-4 bounds are now
source-formalized. The remaining mathematical step is a preserved
root-specific inequality that keeps the blank-root orbit outside these
logarithmic windows.


## Formalization status

The generic output-balance lemma is in DrainLinearTerminalSource.lean as
terminal_output_balance_of_mass, with a drain-specific wrapper
terminal_output_balance_joint. It states |d'-a'|≤K+4 from
a'+d'≤M, 2M+5<3^K, and terminality. These refinements compiled with the
unmodified upstream source imports in pinned CI run 42377763545.

The four branch-specific source theorems are in TerminalRatio4Source.lean.
They compose the evaluator/drain joint-mass bounds, terminal output balance,
and root-ray bridge to prove the four ratio-4 windows. All four compiled in
run 42377763545. The exact 10,000-state scan also passed in that run and again
in run 42378346371.

The generic cancellation step is formalized separately in
TerminalRatio4Arithmetic.lean. Its far/near lemmas prove the ratio-4 interval
from the two bridge-error intervals, the output-balance bound, and the
parity ranges for c_R,c_L. It compiled in pinned CI run 42375801220.

The canonical minimal-budget ray cocycle is source-verified in
CanonicalRayCocycleSource.lean (run 42377437529). The exact identities
connecting canonical terminal gaps to the old-ray distance parameters, and
the conditional terminal-window exclusions, are in
CanonicalRayRootDistanceArithmetic.lean; they passed source CI in run
42378346371. See CanonicalRayCocycle.md for the four canonical bases, finite
distance scans, and the conditional logarithmic-versus-square-root argument.

The all-time old-ray distance invariant remains unproved. No all-time
nonhalting theorem for the blank-root orbit and no exact BB(6) value has been
established.
