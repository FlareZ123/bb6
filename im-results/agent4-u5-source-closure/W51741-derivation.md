# U5 source-only extensions: w=541 and w=445 (mod 2048)

**Status: Lean proof drafts; not compiled or source-certified.** These are additional sparse residual cylinders in the existing U5 high m=0 stopping-root programme. They do not decide Machine C or BB(6), and they do not increase the root-index density.

## 1. Common residual identity

The U5 residual equations imply

\[
211t+1360+22155w=20\cdot2^{201+3360w}.
\]

For each w residue below, the right side is divisible by 2048. The inverse
identity

\[
211\cdot22363=2048\cdot2304+1
\]

then determines t modulo 2048.

## 2. Cylinder w=541 (mod 2048)

The exact constant is

\[
211\cdot1707+1360+22155\cdot541=2048\cdot6029.
\]

Thus t=1707+2048v. Since

\[
43t-1=73400+43\cdot2048v\equiv8\pmod{16},
\]

the exact q-fan has only q=0,1.

### q=0 chain

The q=0 fan parent is

\[
P_0=(73398+88064v,\;72544+87040v).
\]

It is even/even with sum 2 modulo 4, forcing the direct parent

\[
D_0=(145940+175104v,\;36271+43520v).
\]

This state is even/odd with x+y+1 congruent to 4 modulo 8, so the
even/odd-four inverse forces

\[
Q_0=(91103+109312v,\;63686+76416v).
\]

Three six-even-right inverses force

\[
\begin{aligned}
R_1&=(154787+185728v,\;31842+38208v),\\
R_2&=(186627+223936v,\;15920+19104v),\\
R_3&=(202545+243040v,\;7959+9552v).
\end{aligned}
\]

The sums at Q0,R1,R2 are 5,5,3 modulo 8. R3 is odd/odd with sum
8 modulo 16, so its valuation-three parent is

\[
S_0=(105250+126296v,\;56603+67924v),
\]

which is odd-right with sum 1 modulo 4 and hence blank-unreachable.

### q=1 chain

The q=1 fan parent is

\[
P_1=(18348+22016v,\;100066+120064v).
\]

It is even/even with sum 2 modulo 4. Two exact direct inverses give

\[
D_1=(118412+142080v,\;50032+60032v),
\]
\[
D_2=(168442+202112v,\;25015+30016v).
\]

D1 has sum 4 modulo 8; D2 is odd-right with sum 1 modulo 4.
Thus both q branches are excluded and X_t is blank-unreachable for all
t=1707+2048v.

## 3. Cylinder w=445 (mod 2048)

The exact constant is

\[
211\cdot1547+1360+22155\cdot445=2048\cdot4974.
\]

Thus t=1547+2048v and again 43t-1 is 8 modulo 16, leaving q=0,1.

### q=0 chain and sum-seven terminal

The q=0 parent is

\[
P_0=(66518+88064v,\;65744+87040v),
\]

even/even with sum 2 modulo 4. Its forced direct parent is

\[
D_0=(132260+175104v,\;32871+43520v),
\]

even/odd with x+y+1 congruent to 4 modulo 8. The even/odd-four
inverse gives

\[
Q_0=(82563+109312v,\;57716+76416v).
\]

Q0 satisfies all hypotheses of the exact sum-seven parent theorem:
y>=12, x+y=7 modulo 8, x+y+1=8 modulo 16,
x+y+1=24 modulo 32, x=3 modulo 4, and y=4 modulo 8.
Every source parent is therefore odd/odd with sum 2 modulo 4, excluded
by the established blank odd-image invariant.

### q=1 chain

The q=1 parent is

\[
P_1=(16628+22016v,\;90686+120064v).
\]

It is even/even with sum 2 modulo 4. Six exact direct inverses give

\[
\begin{aligned}
D_1&=(107312+142080v,\;45342+60032v),\\
D_2&=(152652+202112v,\;22670+30016v),\\
D_3&=(175320+232128v,\;11334+15008v),\\
D_4&=(186652+247136v,\;5666+7504v),\\
D_5&=(192316+254640v,\;2832+3752v),\\
D_6&=(195146+258392v,\;1415+1876v).
\end{aligned}
\]

The first five direct steps use the even/even sum-two-mod-four
equivalence. The final step uses the sum-four-mod-eight equivalence.
D6 is odd-right with sum 1 modulo 4, so it is blank-unreachable.

Thus X_t is blank-unreachable for all t=1547+2048v.

## 4. Lift to authentic high m=0 roots

The existing residual nonemptiness theorem supplies natural s,m for every
w, with

\[
211s+129=5\cdot2^{201+3360w},\qquad
32s=32+840w+m.
\]

For w=2048n+541 or w=2048n+445, the residual identity forces the
corresponding t-class above. The existing exact M8 terminal fan,
six-even-right residual chain, two-parent A_s feeder, and original m=0
source-parent theorem then give an authentic high stopping root

\[
(2j+3,3j+7),\qquad j=39+64s,
\]

which is blank-unreachable. In both cases the existing root-index identity
still gives j=18791 modulo 32768. These are two additional infinite
parameter subfamilies inside the same containing root residue, not new
root-index arithmetic progressions or density increments. The w=541
cylinder contains the earlier w=51741 modulo 65536 subcylinder.

## 5. Formalization boundary

The declarations are in:

- U5Q0SourceOnlyW1021.lean:
  q0_X_not_reach_t1707mod2048,
  blank_no_sum7_target, and q0_X_not_reach_t1547mod2048;
- U5SourceOnlyHighStopW1021.lean:
  u5_w541_t_param, every_w541_residual_has_unreachable_root,
  u5_w445_t_param, blank_no_u5_residual_m8w_w445,
  blank_no_u5_B_s_m8w_w445, blank_no_u5_A_s_m8w_w445,
  blank_no_high_m0_u5_w445, and every_w445_residual_has_unreachable_root.

The q=0 sum-seven branch uses the exact source-parent theorem
sum7_every_parent_odd_image from HighEvenRightSum7Source.lean. No finite
quotient is used in these derivations. The new declarations have not yet
been compiled with Lean 4.36.0-rc2, and their exported axiom output has
not been inspected. Keep them in im-results/ until the complete import
closure compiles and the axiom audit succeeds. No BB(6) or Machine C
decision follows.
