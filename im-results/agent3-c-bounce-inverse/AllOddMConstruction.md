# Proposed universal odd-parameter Machine C stopping-tower construction

**Agent 3, 2026-11-05. Intermediate mathematical derivation.** The concrete m=1 and m=3 cases are source-certified in Lean. The statement below covering every odd m >= 3 currently has a detailed elementary arithmetic proof; **its uniform quantification has not yet been checked by the Lean kernel**. The finite program verify_odd_m_towers.py is an independent sanity check only. This is a contribution about Machine C, not an exact determination of BB(6).

## Source dependencies

The unchanged Machine C return map is BB6.Agent46.secNext. The source-verified stopping iff is BB6.Agent15.section_halts_iff_parametric in SectionParam.lean, with a high stopping branch

\[
  a=2j+3,\qquad k+j+3m+5=2^{2m+2}(j+3).
\]

The exact affine predecessor theorem is section_sum_one_even_iff_affine; reach_iff_normalize transports true-blank section reachability through forced affine predecessors. The source-verified [ChildATwoDepth.lean](ChildATwoDepth.lean) and [ChildBTwoDepth.lean](ChildBTwoDepth.lean) establish *sharp all-start incoming ancestry depth two* for the full rectangles

\[
A=\{(16u+3,32v+16):u,v\in\mathbb N\},\qquad
B=\{(16u+11,32v+32):u,v\in\mathbb N\}.
\]

Both rectangles are also excluded from the actual blank section orbit by EvenChild.lean.

## Uniform construction

Let \(m\ge3\) be **odd** and \(q,n\in\mathbb N\). Choose one cone label \(E\in\{A,B\}\). Define

\[
H=2^{2m+2},\qquad c=H-1,\qquad C=3(H-m-1).
\]

Write \(e=((m-1)/2)\bmod4\). Set the sector-dependent base depth \(d\) and right residue \(R\) by

\[
(d,R)=
\begin{cases}
(e,16)& E=A,\\
((e+2)\bmod4,0)& E=B.
\end{cases}
\]

Set

\[
L=2^{d+5},\qquad N=3(m+1)+2^d(R+2),\qquad
j_0=(-N)\bmod L,
\]

where the last notation is the unique representative \(0\le j_0<L\). Define the infinite two-parameter tower

\[
J_0=Lq+j_0,\qquad J_{n+1}=HJ_n+C,\qquad
T_E(m,q,n)=(2J_n+3,\;cJ_n+C-2).
\]

**Claim (paper argument):** Every \(T_E(m,q,n)\) is an immediate genuine stopping input of the exact Machine C section map. It is unreachable from the blank-entry section state \((5,1)\). From *arbitrary* section starting states, its longest incoming path has exactly

\[
\boxed{D_E(m,n)+2=d+(2m+2)n+2}
\]

edges. A witness of this length exists; no path with \(D_E(m,n)+3\) edges exists. In particular, both cones provide two-parameter excluded stopping towers for **each** odd \(m\ge3\), with unbounded inverse depth in \(n\).

## Derivation

**1. Stopping criterion.** For \(j=J_n\), let \(a=2j+3\) and \(k=cj+C-2\). Then

\[
k+j+3m+5
 =(c+1)j+C+3m+3
 =Hj+3H=H(j+3).
\]

This is exactly the high stopping branch of the original-source Lean stopping iff. Thus secNext applied to the constructed pair is none for all parameters.

**2. The exact right inverse depth.** Since \(m\ge3\), \(H\) is divisible by \(L\): indeed \(2m+2\ge8\ge d+5\). Consequently \(c\equiv-1\pmod L\) and \(C\equiv-3(m+1)\pmod L\). The definition of \(j_0\) gives

\[
cj_0+C\equiv-j_0-3(m+1)
 \equiv 2^d(R+2)\pmod L.
\]

The added \(cLq\) preserves the congruence. Therefore the integer

\[
r(q)=\frac{c(Lq+j_0)+C}{2^d}-2
\]

satisfies \(r(q)\equiv R\pmod{32}\). Also \(r(q)\ge32\): \(C\ge756\), \(2^d\le8\), and \(j_0,q\ge0\), so \(r(q)\ge92\) by an elementary bound. Hence \(r(q)\) is divisible by four and is a valid affine terminal right counter.

The recurrence obeys the exact identity

\[
cJ_{n+1}+C=c(HJ_n+C)+C
 =H(cJ_n+C).
\]

By induction,

\[
k+2=cJ_n+C=H^n(cJ_0+C)
  =2^{D_E(m,n)}(r(q)+2).
\]

Because \(r(q)\equiv0\pmod4\) and \(r(q)\ge32\), its right counter admits exactly \(D_E(m,n)\) successive forced affine inverse edges. For clarity, an inverse right counter \(z\) follows \(z\mapsto(z-2)/2\) whenever \(z\ge4\) and \(z\equiv2\pmod4\), ending at \(r(q)\equiv0\pmod4\). The process never terminates early. The required first-coordinate gate follows from the next paragraph.

**3. The forced affine gate and the two residues.** Since \(N\) and \(L\) are even, \(j_0\) is even. Since \(m\) is odd, \(C\) is even; therefore each \(J_n\) is even, making \(a=2J_n+3\equiv3\pmod4\). Every inverse affine step preserves this first-coordinate residue: \(a\mapsto a+k-2\) with \(k\equiv2\pmod4\) maps 3 to 3 mod 4. The source condition \((a+k)\bmod4=1\) holds at each step.

The exact source-verified normalization mass identity is

\[
x+2r(q)+4D_E(m,n)=a+2k
       =2HJ_n+6H-6m-7,
\]

where \(x\) is the terminal normalized first coordinate. As \(H\) is divisible by 16 and \(r(q)\) by 16, one obtains

\[
x\equiv-6m-7-4d\pmod{16},
\]

since \(2m+2\) is divisible by four. For \(E=A\), \(d\equiv(m-1)/2\pmod4\), giving
\(x\equiv-8m-5\equiv3\pmod{16}\) because \(m\) is odd. For \(E=B\), \(d\) is two greater modulo four, giving \(x\equiv11\pmod{16}\). Combined with \(r(q)\equiv R\pmod{32}\), the normalized pair lies in the exact A or B rectangle.

**4. True-blank nonreachability.** The existing kernel-verified reach_iff_normalize equivalence reduces reachability of each stopping input to its terminal normalized pair. Both A and B rectangles are source-certified absent from the real blank-entry section orbit. Hence none of the constructed stopping inputs is reached from \((5,1)\).

**5. Exact all-start longest ancestry.** At every one of the \(D_E(m,n)\) forced affine inverse stages, the source section predecessor is unique and the corresponding forward edge genuinely exists, by section_sum_one_even_iff_affine. After pulling back those edges, any proposed \(D_E(m,n)+3\)-edge incoming path would give a three-edge incoming path into its A/B normalized pair, contrary to child_A_no_three or child_B_no_three. Conversely, child_A_two_witness and child_B_two_witness provide two source-real incoming edges to the normalized pair. Appending the \(D_E(m,n)\) forced affine forward edges supplies an actual incoming path of length \(D_E(m,n)+2\). This establishes the claimed sharp maximum.

## Reproduction and checked instances

The arithmetic verifier [verify_odd_m_towers.py](verify_odd_m_towers.py) evaluates exact integers for odd \(m=3,\ldots,101\), each cone, \(q=0,1,2\), and \(n=0,1,2\). All 900 samples passed the stop equation, exact affine depth, and normalized-cone tests. This numerical check supports development, and is not used as evidence for universal quantification.

The \((m,d_A,d_B,j_{0,A},j_{0,B})\) initial examples are

| m | d(A) | d(B) | j0(A) | j0(B) |
|---|---:|---:|---:|---:|
| 3 | 1 | 3 | 16 | 228 |
| 5 | 2 | 0 | 38 | 12 |
| 7 | 3 | 1 | 88 | 36 |
| 9 | 0 | 2 | 16 | 90 |
| 11 | 1 | 3 | 56 | 204 |

For \(m=3\), the A specialization is [HighTower3A.lean](HighTower3A.lean) with recurrence \(J_{n+1}=256J_n+756\), seed \(J_0=64q+16\), exact depth \(8n+1\). The B specialization is [HighTower3B.lean](HighTower3B.lean), seed \(256q+228\), exact depth \(8n+3\). The associated all-root sharp-depth modules are [HighTower3ASharp.lean](HighTower3ASharp.lean) and [HighTower3BSharp.lean](HighTower3BSharp.lean). The \(m=1\) towers [HighTowerA.lean](HighTowerA.lean) and [HighTowerB.lean](HighTowerB.lean) require separate modular seed arithmetic because \(H=16\) is insufficient for the simplifying \(H\equiv0\pmod{2^{d+5}}\) used here.

## Status and priority

The concrete \(m=1\) and \(m=3\) theorems are covered by manual source-verified Lean workflows. The displayed all-odd-\(m\) construction is a fully worked arithmetic argument in this note, with the formal Lean theorem itself still pending. In particular, the paper argument relies on existing Lean-verified source lemmas and on elementary modular calculations that have yet to be encoded uniformly.

**Important limit:** This constructs excluded subsets of stopping families for every odd high parameter. It does not exclude all stopping inputs, decide Machine C's actual blank-orbit behavior, or yield an upper bound for all six-state Turing machines. The main next task is a source-connected uniform Lean formalization, followed by an exhaustive account of all remaining high stopping parameters and even/low branches. Do not promote this interim construction to results/ merely because it is infinite or algebraically general.
