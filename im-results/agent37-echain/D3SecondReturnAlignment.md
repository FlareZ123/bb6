# Depth-three P2 second-return alignment

**Status:** the arithmetic alignment below is kernel-checked locally with Lean 4.36.0-rc2 in the accompanying Lean file. The original-source composition that uses it remains an uncompiled candidate. This is a prepared-packet result, not blank-tape reachability or a BB(6) bound.

## Exact depth-three family

Put
\[
M=3^{87}=323257909929174534292273980721360271853387,
\]
\[
s_0=202789636786509251933665269483979866281743,\qquad
P_0=1315608.
\]
For every \(v\geq0\), define
\[
s=s_0+Mv,\quad k=729s+310,\quad h=54s+23,\quad
t=4096s+1744,\quad k_A=64t+45.
\]
Equivalently,
\[
k=147833645217365244659641981453821322519390957+3^{93}v.
\]

The exact arithmetic identities are
\[
2k+1=3^3h,\qquad 1+4\cdot8^3h=27t+17,
\]
and the A-marker endpoint index is
\[
A=8k_A+28
 =893316+2^{21}s
 =24956+3^{87}(1315608+2^{21}v).
\]
All these parameter identities, including the final 86-step shift alignment below, are proved for arbitrary \(v\) in the Lean file.

## Intended original-source route

Use the prepared input packet \(M(3k+4,3,2;0\,1^6)\), where the finite suffix \(0\,1^6\) is followed by blanks, and the P2 marker \(Y_3=01010111\).

1. The P2 reset with \(Q=3\) gives \(M(8k+5,0,12;Y_3)\). The identity \(2k+1=27h\) makes this the depth-three E-chain input \(M(1+4\cdot3^3h,0,3\cdot3+3;Y_3)\).
2. Three E-chain steps give \(M(1+4\cdot8^3h,6,3;Y_3)=M(27t+17,6,3;Y_3)\).
3. Two B edges, preserving the suffix parameter \(p=3\), give \(M(3k_A+3,4,3;Y_3)\).
4. The A marker uses code(4,1); its word increment is \(4+4=8\). The resulting physical regular section is \(L(8k_A+28,2,2)=L(A,2,2)\).

The component source lemmas are already present (e_two_reset, chain_return, b_twice, and close_zero). The complete depth-three wrapper and its exact endpoint bridge have not yet passed a full-source Lean compile and transitive axiom audit.

## Alignment with the 86-step seed

Let
\[
P(v)=1315608+2^{21}v,\qquad p_{\rm shift}=3P(v).
\]
Then
\[
A=24956+3^{86}p_{\rm shift}.
\]
Thus the depth-three endpoint is exactly the inputLift of the base section \(L(24956,2,2)\) for the 86-step DRegular shift theorem.

The existing candidate base trajectory is
\[
L(24956,2,2)\xrightarrow{86\ {\rm DRegular\ steps}}
L(107283033157493534200791430928221345342090,5,1),
\]
where the right-hand unary parameter is \(3K_{\rm exit}+4\) and
\[
K_{\rm exit}=35761011052497844733597143642740448447362.
\]
Under the 3-adic shift, the output becomes
\[
L(3(K_{\rm exit}+8^{86}P(v))+4,5,1).
\]
The q=5 safe-E canonical closure would then return to a canonical source section. The exact input/output shift identities are proved in the Lean file; the base 86-step DRegular certificate and ExceptionalESafeCanonical wrapper are still uncompiled candidates.

Consequently, if those source dependencies pass the full local preflight and original-source audit, this gives an infinite second-return family of prepared P2 packets indexed by \(v\). It does not establish that any member is reached from the blank tape.

## General odd-depth pattern

The same arithmetic construction extends beyond depth three. For odd \(d\geq1\), choose
\[
h_d=\begin{cases}
41,&d\equiv1\pmod6,\\
23,&d\equiv3\pmod6,\\
5,&d\equiv5\pmod6.
\end{cases}
\]
Then \(8^d h_d\equiv4\pmod{27}\). Set
\[
Q=\frac{3(d-1)}2,\quad h=h_d+54s,\quad
k=\frac{3^d h-1}{2},\quad
t=\frac{4\cdot8^d h-16}{27}.
\]
The P2 reset leaves \(3d+3\) unary suffix ones; the depth-\(d\) E chain leaves \(p=3\) and \(q=2d\); two B edges reduce \(q\) to \(2d-2\); the A marker with quotient one returns to \(L(A_d(s),2,2)\), where
\[
A_d(s)=512t+4d+376=A_{d,0}+2^{3d+12}s.
\]
Because \(2^{3d+12}\) is coprime to \(3^{87}\), there is a unique residue class \(s_0\pmod{3^{87}}\) for which \(A_d(s_0)\equiv24956\pmod{3^{87}}\). Choosing a sufficiently large representative and then \(s=s_0+3^{87}v\) aligns the endpoint with the same 86-step seed shift. This is an arithmetic generalization; only the depth-three instance is currently formalized in the accompanying Lean file, and the corresponding source compositions remain to be compiled.

## Research limits and next step

- Keep this in im-results: the source composition is not yet accepted.
- Do not conflate the prepared-packet family with the authentic blank-root orbit.
- Next formalization target: specialize reset_double_B_to_A_source_reentry at d=3,Q=3, expose the exact A-marker endpoint L(A,2,2), and compose it with the 86-step DRegular lift and q=5 safe-E closure.
- Run the existing manual source audit only after the complete dependency closure has passed local Lean 4.36.0-rc2 preflight; do not create another workflow.
