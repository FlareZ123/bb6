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


## Root32 branch: exact two-parent closure candidate

For \(r\equiv32\pmod{64}\), write \(u=1802+6720t\). Then
\[
S=67186+999595u
 =32(56291793+209914950t),
\]
where the parenthesized factor is odd. Hence \(v_2(S)=5\), and the general parent fan forces \(n=0\) or \(n=2\).

The corrected exact P4 parents are:
\[
\begin{aligned}
P_0&=(900668686+3358639200t,\;
      494467868+1843895760t),\\
P_2&=(225167170+839659800t,\;
      832218623+3103385460t).
\end{aligned}
\]
The \(n=2\) coordinates include the required half-unit correction: they are obtained from \(w=2+8t\), \(z=w/2=1+4t\), with
\[
a_2=15252220+209914950z,\qquad
k_2=56372258+775846365z.
\]
The earlier expression \(56372258+387923182w\) is incorrect and must not be reused.

The two P4 parents now have a compact closure argument:
- \(P_0\) is even/even with sum \(2\bmod4\). Its complete even/even source fan eliminates the zero-left and even-a bounce branches, leaving the direct parent
  \[
  D_0=(1395136552+5202534960t,\;
       247233933+921947880t),
  \]
  which has odd right coordinate and sum \(1\bmod4\). The existing source-certified blank_no_odd_sum_one theorem excludes \(D_0\), hence \(P_0\).
- \(P_2\) is even/odd, has \(3\mid x+y\), and
  \[
  x+y+1=1057385794+3943045260t\equiv2\pmod4.
  \]
  The complete source grammar forces every predecessor of an even/odd, three-divisible target into the odd-a high-bounce branch, which requires \(4\mid x+y+1\). Thus \(P_2\) has no source predecessor and cannot be blank-reachable.

The corresponding B2 cylinder has an exact source-parent fan with only
\[
(17805+264880u,\;26342+391848u),\qquad
(4449+66220u,\;33017+491178u)
\]
as possible parents. The second is odd/odd with right coordinate at least five and sum \(2\bmod4\), so blank_no_odd_sum_two excludes it. The first is odd/even with sum \(3\bmod8\), so two applications of section_odd_even_iff_affine and one application of blank_reach_iff_even_right force the chain
\[
(17805+264880u,26342+391848u)
\to(44145+656728u,13170+195924u)
\to(57313+852652u,6584+97962u)
\to P_4(u).
\]
Consequently the whole \(u=1802+6720t\) B2 cylinder is excluded if the source draft's Lean proofs compile.

**Formalization status:** U5B2Root32.lean now contains the attempted source proofs for both three-divisible parent lemmas, the corrected P4 parent fan, the P4 exclusion, and the composed B2 exclusion. It is an intermediate draft pending local Lean preflight; none of these new declarations should yet be cited as kernel-checked. Agent 6 has been asked for a focused local compile, and Agents 4 and 11 for independent mathematical review. Keep this work in im-results/ until the proof is compiled and its axiom profile checked.


The source draft now also includes the root-index bridge:
- p4_exact_residual_identity derives
  \[
  211S_4+7(2570932352+3163718175r)
  =19991900\cdot2^{E-13}
  \]
  from the exact residual root equation
  \[
  18018+211u+22155r=20\cdot2^{E-13}.
  \]
- p4_sum_mod64_of_root32 uses \(r\bmod64=32\) and \(E=201+3360(6657+8192r)\) to prove \(S_4\bmod64=32\).
- p4_root32_u_parameter then proves \(u=122+840w=1802+6720t\) for some \(t\), since \(S_4=8(15252222+104957475w)\) and \(S_4\bmod64=32\) forces \(w\bmod8=2\).
- blank_no_b2_root32_from_root_index composes the exact root equation, valuation bridge, and B2 exclusion.

The root-index theorem is currently conditional on the exact residual identity being supplied; the Lean draft has not yet been compiled. This separates the arithmetic root-index bridge from the source-orbit exclusion and makes the remaining formalization dependency explicit.

## 19 November update — arbitrary-parameter root32 bridge

The earlier root-index wrapper assumed the intermediate parameterization
u=122+840w. This was a genuine coverage gap: the exact root equation
had not yet been used to derive that parameterization.

The new theorem root32_u_parameter_of_exact in U5B2Root32.lean removes the
assumption. From

    r = 32 (mod 64),
    E = 201+3360(6657+8192r),
    18018+211u+22155r = 20*2^(E-13),

the two exact modular consequences are

    u = 10 (mod 64),    u = 17 (mod 105).

Their CRT gives u=1802+6720t. The stronger theorem
blank_no_b2_root32_from_exact_root_index now composes this bridge with
the existing conditional B2 exclusion, with no pre-parameterization
assumption on u.

**Verification boundary:** the standalone arithmetic bridge was compiled
locally with Lean 4.36.0-rc2; its axiom profile is [propext, Quot.sound],
with no sorryAx. The full U5B2Root32.lean module, including its
original-source parent-fan dependencies and final composed exclusion,
has not yet been compiled. This is an intermediate result only; it does
not close other root-index strata or decide Machine C / BB(6).
