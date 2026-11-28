# Universal adjacent-valuation inverse parity law

**Agent 20, 28 November 2026. Status:** complete elementary **paper proof** for the original-source Space Needle high-level map, plus exact small and multi-step prepared witnesses; not yet an original-source Lean theorem for arbitrary valuation \(v\) and depth \(k\). It gives a structured return-time rule for **every** adjacent pair of valuation labels, unlike a finite hand-picked modular table. It does not address blank-start reachability.

## Exact theorem

Let \(v\in\mathbb N\), \(w=v+1\), and define **signed** affine corrections

\[
L_v=2^{v+1},\qquad
D_v=L_v+3,\qquad
d_v=2^v(2v-3)\in\mathbb Z.
\]

The unchanged Space Needle original high-level successor carries a legal valuation-\(v\) shifted predecessor \(P\) to shifted target \(B\) by the exact equation

\[
L_v B = D_v P + d_v .
\]

Suppose the shifted target \(B\) admits a **legal valuation-\(w\) incoming edge**, and a chain of \(k\) consecutive **legal valuation-\(v\) reverse edges** runs from \(B\) to \(P_k\). Then

\[
\boxed{D_w\mid(3P_k+d_w)
\quad\Longleftrightarrow\quad
k\text{ is even}.} \tag{A}
\]

In particular, every odd-depth ancestor in this monochromatic \(v\)-inverse ray has **no** incoming valuation-\(w\) parent. Every even-depth ancestor **does** have the exact \(w\)-parent congruence; if its shifted counter meets the separately required positivity threshold

\[
P_k\ge 3\cdot2^w+w+3,
\]

then it has an actual legal incoming valuation-\(w\) edge, with nonnegative cofactor \(q\). For every finite even \(k\) there are infinitely many arbitrarily large positive prepared targets for which the entire ray of \(k\) inverse edges is legal and the even-depth \(w\)-parent exists. The truth of the congruence equivalence (A) itself is independent of these size conditions once the \(v\)-chain exists.

Thus **the first possible return is depth exactly 2, uniformly for every adjacent pair \(w=v+1\)**. This is optimal because depth1 is universally forbidden by [the all-valuation upward-separation theorem](UPWARD-SEPARATION.md).

## Stronger form: every residue is a two-cycle or a fixed point

The parity theorem is the \(w\)-parent consequence of a **full residue involution**, without assuming that the starting target has any \(w\)-parent. For \(w=v+1\), define

\[
R_w(B)=3B+d_w\pmod{D_w},\qquad
C_v=2(d_w-d_v)=2^{v+1}(2v+1)\pmod{D_w}.
\]

For *every genuine original-source valuation-\(v\) edge* from shifted parent \(P\) to shifted target \(B\), the following exact **integer** identity holds, where \(R=3B+d_w\), \(S=3P+d_w\), and \(\Delta=d_w-d_v\):

\[
\boxed{3(S+R-2\Delta)=D_w(R-S).} \tag{R}
\]

Indeed, the source edge equation gives \(D_vS-L_vR=3\Delta\), and \(D_w=D_v+L_v\), \(2D_v=D_w+3\), \(2L_v=D_w-3\); doubling and rearranging yields (R). Since \(\gcd(D_w,3)=1\), it follows that

\[
\boxed{R_w(P)\equiv C_v-R_w(B)\pmod{D_w}.} \tag{S}
\]

Thus the exact finite-state residue transition is the **affine reflection** \(r\mapsto C_v-r\), and its square is the identity on *every* residue, not just on residue zero. This identity holds for \(v=0,1\) with **signed** corrections \(d_0=-3,d_1=-2\), and for arbitrary larger valuations.

The offset \(C_v\) is nonzero modulo \(D_w\): \(D_w\) is odd and coprime to the power \(2^{v+1}\), and \(0<2v+1<D_w\), so \(D_w\nmid2^{v+1}(2v+1)\). Because \(D_w\) is odd, reflection has exactly one fixed residue \(r=\Delta\bmod D_w\), and the remaining \(D_w-1\) residues form \((D_w-1)/2\) disjoint 2-cycles. The **unique cycle containing zero** is \(\{0,C_v\}\).

Hence for any legal v-inverse ray starting from *any* shifted target B, there is a complete residue classification of valuation \(w=v+1\) parent availability:

- If \(R_w(B)=0\), only **even** ancestors have the \(w\)-parent congruence.
- If \(R_w(B)=C_v\), only **odd** ancestors have the \(w\)-parent congruence.
- For every other starting residue, **no** ancestor in that monochromatic \(v\)-ray has the \(w\)-parent congruence.

As always, a congruence gives a **legal positive source parent only above** the explicit cofactor threshold. For example, the authentic high-level blank starting shifted counter \(B=3\) has \(R_1(B)=0\bmod7\) but **no** legal valuation-1 incoming predecessor, because \(B<3\cdot2^1+1+3=10\). This emphasizes that modular potential zero is not by itself physical reachability.

[AdjacentReflection.lean](AdjacentReflection.lean) contains a generic exact Lean identity and nonzero-offset proof candidate. [AdjacentReflectionSource.lean](AdjacentReflectionSource.lean) connects the reflection identity to **all natural valuations of the original Cryptids Space Needle high-level map**, including the signed low cases. Both are authored and in the existing manual source-CI proof gate but **not yet kernel-accepted**. Their arithmetic is independently corroborated by direct exact transitions for valuations \(v=0,\dots,44\) with 20 cofactor choices each (900 genuine original-source edges).

## Proof

The generic **signed** affine potential, valid even for \(v=0,1\), satisfies

\[
L_v^k(3B+d_v)=D_v^k(3P_k+d_v).
\]

The exact cross-potential identity (obtained by adding/subtracting \(d_w\)) is

\[
D_v^k(3P_k+d_w)-L_v^k(3B+d_w)
  =(D_v^k-L_v^k)(d_w-d_v). \tag{1}
\]

For adjacent labels \(w=v+1\),

\[
D_w=2^{v+2}+3=D_v+L_v.
\]

Both \(D_v\) and \(L_v\) are coprime to \(D_w\): \(\gcd(D_v,D_w)=\gcd(D_v,3)=1\) and \(\gcd(L_v,D_w)=1\) because \(L_v\) is a power of two and \(D_w\) is odd. The target's \(w\)-parent gives \(D_w\mid3B+d_w\). Reducing (1) modulo \(D_w\) therefore gives

\[
D_w\mid3P_k+d_w
\iff D_w\mid(D_v^k-L_v^k)(d_w-d_v).
\]

Now \(D_v\equiv-L_v\pmod{D_w}\), so the latter condition is

\[
D_w\mid \bigl((-1)^k-1\bigr)L_v^k(d_w-d_v).
\]

If \(k\) is even, the integer is zero. If \(k\) is odd, it is \(-2L_v^k(d_w-d_v)\). As \(D_w\) is odd and coprime to \(L_v\), odd-\(k\) divisibility would force \(D_w\mid d_w-d_v\), contradicted by the [universal upward-separation arithmetic theorem](UPWARD-SEPARATION.md), which proves \(D_w\nmid3(d_w-d_v)\) for **every** \(v<w\) (hence a fortiori \(D_w\nmid d_w-d_v\)).

For **every finite even \(k\)**, choose \(B\) via CRT from the coprime congruences

\[
3B+d_v\equiv0\pmod{D_v^k},\qquad
3B+d_w\equiv0\pmod{D_w}.
\]

All \(D_j\) are odd and coprime to 3, and \(\gcd(D_v,D_w)=1\). The inverse map \(T_v(B)=(L_vB-d_v)/D_v\) is integral at every depth because the first congruence provides the full \(D_v^k\) divisibility and the fixed-point transport identity moves one factor of \(D_v\) per step. For sufficiently large representatives of the CRT progression, all \(k\) inverse steps have \(P_j=2^v(2q_j+3)\) with \(q_j\ge0\), and every even-depth \(w\)-predecessor has \(q\ge0\) as well. Thus the alternating return pattern is **attainable at arbitrary size**, not an artifact of a relaxed residue graph.

No conclusion about *actual blank-tape reachability* follows.

## Tiny exact original-equation witness, including valuation zero

For \(v=0\), \(w=1\), choose shifted target \(B=101\). Its genuine valuation-0 incoming predecessors form the 2-edge inverse chain

\[
101\xleftarrow{v=0}41\xleftarrow{v=0}17,
\]

since \(2(101)=5(41)-3\) and \(2(41)=5(17)-3\). The target also has a valuation-1 incoming predecessor \(58\), because \(4(101)=7(58)-2\). Its intermediate ancestor \(41\) does **not** have an incoming valuation-1 predecessor, since \(4(41)+2=166\) is not divisible by 7. The depth-two ancestor \(17\) has valuation-1 predecessor \(10\), because \(4(17)=7(10)-2\). All predecessors satisfy the exact source shape \(P=2^v(2q+3)\) with \(q\ge0\), and all indicated forward high-level steps strictly increase shifted counters.

A longer four-edge witness is

\[
5001\xleftarrow{0}2001\xleftarrow{0}801\xleftarrow{0}321\xleftarrow{0}129;
\]

valuation-1 parents exist at shifted counters \(5001,801,129\) and do not exist at \(2001,321\). Exact integer code in [mixed_branch_audit.py](mixed_branch_audit.py) can be extended to check these examples.

## Relationship to broader BB(6) work

The theorem proves a **universal, all-depth, exact phase law** in the original accelerated Space Needle inverse grammar. Unlike the 42-case return table of the [main dossier](README.md), it includes valuations zero and one and has no bound on the number of inverse steps. It explains precisely why an immediate upward-label obstruction cannot be iterated naively to claim the disappearance of larger-label parents: for adjacent labels they **recur every two reverse edges**. As such it provides both a sound pruning rule for odd depths and a mathematically exact parity-compression for inverse enumerators.

The main open problem remains an all-time invariant or finite exhaustive root proof for the **actual** blank start \(B=3\); this result does not provide that missing quantifier.
