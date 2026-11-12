# Five-shallow dyadic barrier: model-level derivation

**Status:** conditional mathematical derivation; the Lean files exist but have not yet been compiled, and there is no five-shallow source lift. Do not treat this as a source-certified P1 theorem.

## Scalar normal form

Let \(P=2^n\), \(q=8^s\), \(qp=P\), and \(qd=14n+92\). Put \(e=n-3s\) and \(X=n+2\). For five shallow edge types \(\tau_i\in\{0,1\}\) and intervening depth-two run lengths \(u,v,w,x,r\), set
\[
A_1=2^\alpha8^u=2^{e_1},\quad
A_2=2^\beta8^v=2^{e_2},\quad
A_3=2^\gamma8^w=2^{e_3},\quad
A_4=2^\delta8^x=2^{e_4},\quad
A_5=2^\epsilon8^r=2^{e_5},
\]
where \(e_1=\alpha+3u\), \(e_2=\beta+3v\), \(e_3=\gamma+3w\), \(e_4=\delta+3x\), and \(e_5=\epsilon+3r\). The exact profile table is
\[
\tau=0:\;(\alpha,C,L,O)=(1,588,84,232),\qquad
\tau=1:\;(\alpha,C,L,O)=(2,392,56,136).
\]
In particular every \(e_i\ge1\).

The cumulative times are
\[
T_1=n+6+3s,\qquad T_{i+1}=T_i+e_i,
\]
and the five source profiles give
\[
R_1=L_1T_1-O_1-d,\qquad R_i=L_iT_i-O_i\ (2\le i\le5),\qquad E=112T_6-384.
\]
The exact terminal-wall equation is
\[
Kp=A_1\big(A_2\big(A_3\big(A_4(A_5E+R_5)+R_4\big)+R_3\big)+R_2\big)+R_1,
\]
with
\[
K+98=C_1q+C_2qA_1+C_3qA_1A_2+C_4qA_1A_2A_3+C_5qA_1A_2A_3A_4.
\]

## Raw remainder bounds and quotient halving

Assume \(n\ge83\). Since \(q\mid14n+92\), \(q\le14n+92\le15X\), and \(d\le14n+92\). Also \(T_i\ge n+6\), so
\[
R_1\ge56(n+6)-232-(14n+92)=42n+12>0,
\]
and for \(i\ge2\),
\[
R_i\ge56(n+6)-232=56n+104>0.
\]

When the preceding exponents sum to at most \(e\), \(T_i\le2n+6\). The exact profile correlation now improves the upper bound to \(R_i\le168X\): for \(\tau_i=0\),
\[
R_i\le84(2n+6)-232=168n+272\le168(n+2),
\]
while for \(\tau_i=1\),
\[
R_i\le56(2n+6)-136=112n+200\le168(n+2).
\]
The same bound applies to \(R_1\), since it has the additional subtraction of \(d\).

At the \(i\)-th dyadic peel, the elementary remainder lemma gives \(S_i=2^{e_i}d_i\) and \(A_i=2^{e_i}\le S_i\). Because \(e_i\ge1\), it also gives \(2d_i\le S_i\). Consequently,
\[
S_1=R_1\le168X,\qquad d_1\le84X,\qquad S_2=R_2+d_1\le252X,
\]
\[
d_2\le126X,\qquad S_3=R_3+d_2\le294X,\qquad d_3\le147X,
\]
\[
S_4=R_4+d_3\le315X,\qquad d_4\le158X,\qquad S_5=R_5+d_4\le326X.
\]
Thus \(A_1\le168X\), \(A_2\le252X\), \(A_3\le294X\), \(A_4\le315X\), and \(A_5\le326X\).

The scaled remainder bounds are
\[
qS_1\le2520X^2,\qquad qA_1S_2\le635040X^3,
\]
\[
qA_1A_2S_3\le186701760X^4,\qquad
qA_1A_2A_3S_4\le58811054400X^5,
\]
and
\[
qA_1A_2A_3A_4S_5
\le15\cdot168\cdot252\cdot294\cdot315\cdot326\,X^6
=19172403734400X^6.
\]

## Sixth-power gap and contradiction

The exact gap
\[
19172403734400(n+2)^6<2^n
\]
holds for every \(n\ge83\): it fails at \(n=82\), while at \(n=83\) the two sides are \(7230862781795901150000000\) and \(9671406556917033397649408\), respectively. Check \(n=83,84,85,86,87,88\), then induct in steps of six using \(n+8\le2(n+2)\).

After four peels, the terminal equation is
\[
K2^{e-e_1-e_2-e_3-e_4}=A_5E+S_5.
\]
The fifth peel gives \(A_5\le S_5\le326X\). Since \(T_6\le2n+6\) and \(E=112T_6-384\),
\[
E+1\le224n+289\le224(n+2)=224X.
\]
Therefore
\[
K2^{e-e_1-e_2-e_3-e_4}
\le S_5(E+1)\le326X\cdot224X=73024X^2.
\]
On the other hand, \(K+98\) is the sum of the five positive coefficient terms. The preceding terms already include \(C_1q\ge392>98\), so subtracting 98 still leaves at least the final term; hence
\[
K\ge C_5qA_1A_2A_3A_4\ge392qA_1A_2A_3A_4.
\]
Since
\[
qA_1A_2A_3A_4\cdot2^{e-e_1-e_2-e_3-e_4}=2^n,
\]
the same quantity is at least \(392\cdot2^n\). The sixth-power gap implies \(73024X^2<2^n\), a contradiction.

## Formalization state

- FiveLayerGap.lean contains the \(n\ge83\) sixth-power gap.
- FiveLayerBarrier.lean encodes the five-peel conditional barrier, using the exact two-profile correlation and the quotient-halving consequence \(2d_i\le S_i\).
- FiveShallowProfileBounds.lean formalizes the exact-profile estimate \(1\le\alpha\) and \(0<LT-O\le168(n+2)\).
- FiveShallowIntegerAlgebra.lean encodes the five-layer telescoping identity from the coefficient and terminal-wall equations.
- The targeted CI compile is in progress. The source lift remains pending: adapt [FourShallowSourceModel.lean](FourShallowSourceModel.lean) to five profiles and six depth-two segments, then adapt [FourShallowSourceLift.lean](FourShallowSourceLift.lean) with an exact-five no-wall theorem. The existing stepwise proof pattern should then give `source_low_trace_wall_needs_six_shallows` for n>=83 by splitting the shallow count at five.
