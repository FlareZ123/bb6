# U5 source-only extension: w=51741 (mod 65536)

**Status: Lean proof draft; not compiled or source-certified.** This is an additional sparse residual cylinder in the existing U5 high m=0 stopping-root programme. It does not decide Machine C or BB(6), and it does not increase the root-index density.

## 1. Residual parameter

The U5 residual equations imply the exact identity

\[
211t+1360+22155w=20\cdot2^{201+3360w}.
\]

If w is congruent to 51741 modulo 65536, the right side is divisible by 65536. The exact constants

\[
211\cdot1707+1360+22155\cdot51741=65536\cdot17497,
\]
\[
211\cdot22363=65536\cdot72+1
\]

therefore force t to be congruent to 1707 modulo 65536. Write

\[
t=1707+65536v.
\]

Then

\[
43t-1=73400+43\cdot65536v\equiv8\pmod{16}.
\]

In the exact original-source fan for X_t=(44t-1,42t-1), every parent has
43t-1=4^q U with U even. The congruence modulo 16 rules out q>=2,
leaving exactly the two cases q=0,1.

## 2. q=0 source-parent chain

The q=0 fan parent is

\[
P_0=(73398+2818048v,\;72544+2785280v).
\]

It is even/even with coordinate sum 2 modulo 4. The complete even/even parent fan therefore forces the direct parent

\[
D_0=(145940+5603328v,\;36271+1392640v).
\]

This state is even/odd and satisfies x+y+1 congruent to 4 modulo 8.
The exact even/odd-four inverse forces

\[
Q_0=(91103+3497984v,\;63686+2445312v).
\]

The next three states are forced by the exact six-even-right inverse:

\[
\begin{aligned}
R_1&=(154787+5943296v,\;31842+1222656v),\\
R_2&=(186627+7165952v,\;15920+611328v),\\
R_3&=(202545+7777280v,\;7959+305664v).
\end{aligned}
\]

The sums x+y at Q0,R1,R2 are respectively 5, 5, and 3 modulo 8,
so each six-even-right inverse is in its exact uniqueness sector. At
R3, both coordinates are odd and x+y is 8 modulo 16. The exact
odd/odd valuation-three inverse forces

\[
S_0=(105250+4041472v,\;56603+2173568v).
\]

Here the right coordinate is odd and x+y is 1 modulo 4, which is
excluded from the authentic blank-section orbit by the established
odd-image invariant.

## 3. q=1 source-parent chain

The q=1 fan parent is

\[
P_1=(18348+704512v,\;100066+3842048v).
\]

It is even/even with sum 2 modulo 4, so its only possible source parent is

\[
D_1=(118412+4546560v,\;50032+1921024v).
\]

This is even/even with sum 4 modulo 8, so the stronger exact parent
lemma again forces the direct parent

\[
D_2=(168442+6467584v,\;25015+960512v).
\]

The right coordinate of D2 is odd and its coordinate sum is 1 modulo 4.
The same blank odd-image invariant excludes it.

Both possible q branches therefore contradict blank reachability. This
establishes the source-only exclusion of X_t for all t=1707+65536v,
provided the added Lean draft compiles against the exact transitive
source closure.

## 4. Lift to authentic high m=0 roots

The existing residual nonemptiness theorem supplies natural s,m for every
w, satisfying

\[
211s+129=5\cdot2^{201+3360w},\qquad
32s=32+840w+m.
\]

For w=65536n+51741, the residual identity forces the t-class above. The
existing exact M8 terminal fan, six-even-right residual chain, two-parent
A_s feeder, and original m=0 source-parent theorem then give an authentic
high stopping root

\[
(2j+3,3j+7),\qquad j=39+64s,
\]

which is blank-unreachable. The existing root-index identity still gives

\[
j\equiv18791\pmod{32768}.
\]

This is an additional infinite parameter subfamily inside the same
containing root residue. It is disjoint from the previously listed
w-cylinders, but it is not a new root-index arithmetic progression or
density increment.

## 5. Formalization boundary

The declarations are in:

- im-results/agent4-u5-source-closure/U5Q0SourceOnlyW1021.lean:
  q0_X_not_reach_t1707mod65536;
- im-results/agent4-u5-source-closure/U5SourceOnlyHighStopW1021.lean:
  u5_w51741_t_param, blank_no_u5_residual_m8w_w51741,
  blank_no_u5_B_s_m8w_w51741, blank_no_u5_A_s_m8w_w51741,
  blank_no_high_m0_u5_w51741, and
  every_w51741_residual_has_unreachable_root.

They reuse the exact original-source parent fan and inverse equivalences;
no finite quotient is used in this derivation. The new declarations have
not yet been compiled with Lean 4.36.0-rc2, and their exported axiom
output has not been inspected. Keep them in im-results/ until the complete
import closure compiles and the axiom audit succeeds. No BB(6) or Machine C
decision follows.
