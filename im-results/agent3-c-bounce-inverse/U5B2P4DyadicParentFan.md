# U5 B2 residual P4: a root-index-bounded odd/odd parent fan

**Status:** exact paper-level source-parent reduction from the complete original-section grammar. The new general lemma below has not yet been Lean-formalized or compiled. It is a necessary-parent theorem, not a blank-reachability exclusion.

## Residual target and root data

On the remaining even-parameter B2 branch, the target is

\[
P_4(u)=(x,y)=(63895+950614u,\;3291+48981u),
\]
with the authentic residual constraints
\[
u\equiv122\pmod{420},\qquad u+r\equiv2\pmod8.
\]
Here \(r\) is the original root index. This note treats the **\(r\equiv0\pmod8\) subbranch** of the remaining \(u\equiv2\pmod4\) sector. On this subbranch \(u\equiv2\pmod8\), hence \(u\equiv122\pmod{840}\). The complementary \(r\equiv4\pmod8\) subbranch has \(u\equiv6\pmod8\), so \(v_2(S)=2\) and is the separate low-valuation case handled by OddOddLowVal.

Put
\[
S=x+y=67186+999595u.
\]
The congruences \(u\equiv122\pmod{420}\) and \(u\equiv2\pmod8\) give:
- \(x,y\) are odd and \(y\ge5\);
- \(3\mid x\) and \(3\mid y\), hence \(3\mid S\);
- \(8\mid S\), since \(u\equiv2\pmod8\).

The exact second root-index valuation already derived in [U5B2ResidualMod105.md](U5B2ResidualMod105.md) is
\[
\boxed{v_2(S)=v_2(2570932352+3163718175r).}
\]
Its affine-term domination proof is recorded there; this note uses the identity, not a new numerical replay.

## General odd/odd source-parent fan

The following lemma is a direct consequence of the complete original-source grammar BB6.Agent46.section_preimage_all_iff.

**Lemma (three-divisible odd/odd target).** Suppose \(x,y\) are odd, \(y\ge5\), \(3\mid x+y\), and
\[
\operatorname{secNext}(a,k)=(x,y).
\]
Then \(a\) is even and there is an even natural number \(n\) such that
\[
x+y=2^n(2a+4),\qquad 2k+a+7+3n=x+2y.
\]
Consequently \(n+2\le v_2(x+y)\).

**Proof by exhaustive source cases.**
1. The \(a=0\) exceptional rows have right coordinate at most four. Its nonexceptional branch requires \(x+y=8\cdot2^n\), impossible because \(3\mid x+y\).
2. The \(a=1\) exceptional rows are incompatible with \(x\) odd, \(y\ge5\). Its remaining branch requires \(x+y+1=16\cdot2^n\), impossible because \(x+y+1\) is odd.
3. The \(k=0\) row has right coordinate two. The direct branch has even right coordinate. Both are excluded.
4. The odd-\(a\) bounce branch requires \(x+y+1=2^n(2a+6)\), again impossible because the left side is odd and the right side is even.
5. Only the even-\(a\) bounce branch remains. Its exact source equations simplify to
   \[
   x+y=2^n(2a+4),\qquad 2k+a+7+3n=x+2y.
   \]
   Since \(x+2y\) is odd, while \(a\) is even, the second equation forces \(n\) even. Since \(4\mid2a+4\), the first gives \(2^{n+2}\mid x+y\), hence \(n+2\le v_2(x+y)\). \(\square\)

For a fixed \(n\), the two displayed equations determine at most one parent:
\[
a=\frac{S}{2^{n+1}}-2,\qquad
k=\frac{x+2y-a-7-3n}{2}.
\]
Thus the complete source grammar leaves at most
\[
\boxed{\left\lfloor\frac{v_2(S)}2\right\rfloor}
\]
candidate parent depths, namely \(n=0,2,4,\ldots\le v_2(S)-2\). This is a finite fan for every fixed root index, even though its size is not uniformly bounded as \(r\) varies.

## Exact root-index stratification

Write \(r=8t\). Also write \(u=122+840w\). Then
\[
2570932352+3163718175r
=8(321366544+3163718175t),
\]
and \(v_2(321366544)=4\), while \(3163718175\) is odd. Therefore, whenever \(v_2(t)<4\),
\[
v_2(S)=3+v_2(t).
\]
In particular:
- \(r\equiv8\pmod{16}\) gives \(v_2(S)=3\), so only \(n=0\) can occur. Equivalently \(w\) is odd and \(u\equiv2\) or \(18\pmod{32}\). This is exactly the unique-parent valuation-three layer covered by OddOddVal3Orbit.
- \(r\equiv16\pmod{32}\) gives \(v_2(S)=4\), so only \(n=0,2\) can occur. Equivalently \(w\equiv0\pmod4\) and \(u\equiv26\pmod{32}\). This is the two-parent sum-16 layer covered by MixedOdd16TwoOrbit.
- \(r\equiv32\pmod{64}\) gives \(v_2(S)=5\), so again only \(n=0,2\) can occur, with \(w\equiv2\pmod4\) and \(u\equiv10\pmod{32}\).
- \(64\mid r\) gives \(v_2(S)\ge6\); it corresponds to \(w\equiv2\pmod4\) with a higher lift, and the admissible even depths extend to \(n=4\) and beyond according to the exact affine valuation.

The valuation identity therefore converts the unbounded-looking P4 inverse problem into a root-index-indexed finite dyadic parent fan. It does not yet show that any of these parents is blank-unreachable.

## Next mathematical obligation

For each admissible even depth \(n\), analyze the explicitly determined even-first-coordinate parent
\[
S=67186+999595u,\quad x=63895+950614u,\quad y=3291+48981u,\\
a_n=\frac{S}{2^{n+1}}-2,\quad
k_n=\frac{x+2y-a_n-7-3n}{2}.
\]
The next step is to intersect these parent families with the already source-certified even/even parent grammars and blank-image restrictions. In particular, distinguish the \(n=0\) and \(n=2\) branches from the genuinely new \(n\ge4\) tail. Do not claim P4 unreachable, or promote this note to results/, until every admissible parent depth is closed by a source proof.
