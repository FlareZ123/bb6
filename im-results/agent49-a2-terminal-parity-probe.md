# A=2 terminal diagnostic: odd-width gap

**Status:** targeted deterministic simulation only; not a proof of non-halting or of a terminal failure.

The current z=1 diagnostic `im-results/agent48-counted-inc0/a2_terminal_basecase_z1.js`
restricts (L\in\{2,4,6\}), so every tested (L) is even. Its marker-0
terminal formula is
[
 a_{term}=\frac{2^{L+7}-35}{3},\qquad L_{term}=L+4.
]
The numerator is divisible by 3 exactly when (L) is even. This leaves
the odd-width case untested.

The blank root does begin at `S1(3,7,2,6,0,63)`, but that is **not**
the width parameter of the later authentic A=2 terminal branch. The
root's marker-1 middle-34 endpoint has
`tm63Length1 = 76` (see
`im-results/agent44-tm63-middle/README.md` and
`im-results/agent42-outer-lcinc/TM63Length1Parity.lean`). The first-Q4
outer-width recurrence keeps its own (L) fixed while replacing (A)
by (A-2), so the authentic later A=2 branch uses (L=76), not 3.
Its terminal width (L+4=80) is even; the marker-0 formula is integral.
Thus this odd-(L) probe is a generic boundary test, **not** a
counterexample to the authentic root route.

I replayed the same sparse-tape A=2 q4Tail-to-S0 input with the
non-root parameter (z=1,L=3):
- (m=16,n=2,K=6,H=24);
- initial state 3 at head 24, with left side
  (d_0\Vert d_1^6\Vert markerWord(0)\Vert d_0^2\Vert d_1^2
    \Vert d_0^4\Vert lh), and right side (s0RightFacing(0));
- 20,000,000 deterministic TM steps;
- 61 visits to the state-4/head-1 window `11110000`, first at
  steps 337, 913, 1593, 2413, 3349 and last at 206601, 213937,
  221413, 229005, 236749, 244597, 252585, 260689;
- no halt within the limit; at the limit the machine is in state 3,
  head 6336, with 5791 nonblank cells.

For this non-root odd width (L=3), the marker-0 formula gives
[
(2^{10}-35)/3=989/3,
]
so it does not define an integer terminal unary parameter. This only
shows that the tested marker-0 formula has a parity condition; it does
not prove that this run never halts, and it does not rule out a
different marker-2 terminal pattern. Since the authentic root width is
(L=76), the parity condition itself is satisfied there. The remaining
gap is the actual positive-(z) proof (the root has (z\ge3)), not an
odd-width obstruction.

The executable replay is
`agent49-a2-terminal-parity-probe.js`. The immediate mathematical
question is whether the authentic A=2 route has a marker-2 terminal
interface (or an additional marker conversion), rather than the
marker-0 SectionBits pattern used by the even-(L) diagnostic.
