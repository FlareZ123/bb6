# U5 B2: new root-index cylinder r = 20 (mod 128)

**Status:** new paper-level infinite exclusion derived on 2026-11-19. The arithmetic has been checked exactly with integer arithmetic, but the composition has **not** been written as a Lean theorem or compiled against the complete original-source import closure. Keep this in `im-results/`; do not report it as source-certified or promote it to `results/`.

## Proposed theorem

Assume natural numbers \(r,E,u\) satisfy
\[
r\equiv20\pmod{128},\qquad
E=201+3360(6657+8192r),
\]
and the exact B2 residual root equation
\[
18018+211u+22155r=20\cdot2^{E-13}.
\]
Then the B2 state is not in the genuine blank section orbit:
\[
\neg CReach(734+10944u,\;34881+518816u).
\]

This is a conditional root-index cylinder exclusion, not a decision for Machine C or BB(6).

## 1. Convert the root index to the P4 parameter

The locally compiled arithmetic lemma
`BB6.Agent3U5B2Root32ParameterBridge.root_equation_mod1680`
gives
\[
(u+105r)\bmod1680=122.
\]
Write \(r=128q+20\). Then \(105r\equiv420\pmod{1680}\), hence
\[
u\equiv1382\pmod{1680}.
\]
Therefore for some \(t\in\mathbb N\),
\[
u=1382+1680t=542+840w,\qquad w=2t+1.
\]
In particular \(u\) is even and \(w\) is odd.

Put \(R=(r-4)/16=8q+1\). Substituting \(r=16R+4\) and \(u=542+840w\) into the exact root equation gives
\[
221000+354480R+177240w=20\cdot2^{E-13},
\]
or, after division by eight,
\[
27625+44310R+22155w=5\cdot2^{E-14}.
\]
Here \(E\ge18\), so the right side is divisible by 16. Reducing modulo 16,
\[
9+6R+11w\equiv0\pmod{16}.
\]
Since \(R\equiv1\pmod8\), this yields \(11w\equiv1\pmod{16}\), and therefore
\[
\boxed{w\equiv3\pmod{16}.}
\]

## 2. Reduce P4 to an even/odd target

The B2-to-P4 implication already drafted in
`U5B2Root32.lean` says that for every even \(u\), B2 reachability implies reachability of
\[
P4(u)=(63895+950614u,\;3291+48981u).
\]
Our \(u=542+840w\) is even.

For this parameterization, the P4 coordinate sum is
\[
67186+999595u=541847676+839659800w.
\]
When \(w=16q+3\), this sum is \(4\pmod{16}\), hence is divisible by four but not by sixteen. The hypotheses of the existing exact theorem
`BB6.Agent3.oddodd_lowval_blank_reach_iff`
are satisfied. It reduces P4 blank reachability to the even/odd target
\[
D(w)=(270923836+419829900w,\;
      148737413+230486970w).
\]

For \(D(w)=(x,y)\),
\[
x+y=419661249+650316870w\equiv0\pmod3,
\]
and
\[
x+y+1=419661250+650316870w.
\]
Substituting \(w=16q+3\) gives
\[
x+y+1=2370611860+10405069920q\equiv4\pmod8.
\]
Thus its exact 2-adic valuation is two. Also \(x\) is even, \(y\) is odd, \(x>5\), and \(y\ge5\).

## 3. The D-parent is forced to depth zero

The drafted exact source-grammar lemma
`even_odd_three_divisible_parent` in `U5B2Root32.lean`
says that any original-section predecessor \((a,k)\) of an even/odd target \((x,y)\) with these parity, size, and mod-three hypotheses satisfies
\[
a\text{ odd},\quad n\text{ even},\quad
x+y+1=2^n(2a+6),\quad
2k+a+7+3n=x+2y.
\]
Because \(a\) is odd, \(4\mid(2a+6)\). The exact valuation
\(v_2(x+y+1)=2\) therefore forces \(n=0\).

Solving the two remaining equations, with \(w=16q+3\), gives the unique possible parent
\[
P=(a,k)=
(1185305927+5202534960q,\;
 1012752124+4445163240q).
\]
It has \(a\) odd, \(k\) even, \(k\ge6\), and
\[
a+k=2198058051+9647698200q\equiv3\pmod8.
\]
The existing exact original-source inverse
`BB6.Agent46.section_odd_even_iff_affine`
then forces the unique predecessor of \(P\) to be
\[
Q=(a+k-2,(k-2)/2)
\]
or, explicitly,
\[
Q=(2198058049+9647698200q,\;
   506376061+2222581620q).
\]
This is odd/odd, its right coordinate is at least five, and
\[
Q_x+Q_y=2704434110+11870279820q\equiv2\pmod4.
\]
The already source-certified invariant
`BB6.Agent11High.blank_no_odd_sum_two`
excludes \(Q\). Hence \(P\), then \(D(w)\), then P4, and finally the B2 state are all blank-unreachable.

## Exact dependencies and validation boundary

The proposed composition uses:
- `root_equation_mod1680` from `U5B2Root32ParameterBridge.lean` (standalone local Lean compilation was reported by Agent 6; the full B2 module remains uncompiled);
- `oddodd_lowval_blank_reach_iff` from `OddOddLowVal.lean`;
- `section_odd_even_iff_affine` from `OddEvenUnique.lean`;
- `blank_no_odd_sum_two` from `HighSumTwo.lean`;
- the draft `even_odd_three_divisible_parent` and `b2_even_reach_implies_p4_reach` in `U5B2Root32.lean`.

The new parent-chain composition is not Lean-compiled. In this invocation, both local `container.exec` and `python.exec` returned a tool-boundary ClientError, so no local exact-source preflight was possible. No CI was dispatched, respecting the current Critic gate. The current `U5B2Root32.lean` import closure must still pass the exact-source preflight and axiom audit before this extension can be accepted.

The new residue class \(r\equiv20\pmod{128}\) is disjoint from the existing \(r\equiv12\pmod{16}\) and \(r\equiv32\pmod{64}\) exclusions.
