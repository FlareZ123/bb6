# Five-shallow dyadic barrier: model-level derivation

**Status:** conditional mathematical derivation; the Lean files exist but have not yet been compiled, and there is no five-shallow source lift. Do not treat this as a source-certified P1 theorem.

## Scalar normal form

Let (P=2^n), (q=8^s), (qp=P), and (qd=14n+92). Put (e=n-3s) and (X=n+2). For five shallow transitions with types (t_i\in\{0,1\}) and intervening depth-two run lengths (u,v,w,x,r), set
[
A_1=2^{\alpha}8^u=2^{t_1},\quad
A_2=2^{\beta}8^v=2^{t_2},\quad
A_3=2^{\gamma}8^w=2^{t_3},\quad
A_4=2^{\delta}8^x=2^{t_4},\quad
A_5=2^{\epsilon}8^r=2^{t_5},
]
where (t_1=\alpha+3u), (t_2=\beta+3v), (t_3=\gamma+3w), (t_4=\delta+3x), and (t_5=\epsilon+3r).

The cumulative times are
[
T_1=n+6+3s,\quad T_{i+1}=T_i+t_i,
]
and the five source profiles ((C_i,L_i,O_i)) give
[
R_1=L_1T_1-O_1-d,qquad R_i=L_iT_i-O_i (2\le i\le5),qquad E=112T_6-384.
]
The exact terminal-wall equation is
[
Kp=A_1\big(A_2\big(A_3\big(A_4(A_5E+R_5)+R_4\big)+R_3\big)+R_2\big)+R_1,
]
with
[
K+98=C_1q+C_2qA_1+C_3qA_1A_2+C_4qA_1A_2A_3+C_5qA_1A_2A_3A_4.
]
All profile coefficients satisfy (392\le C_i\le588), (56\le L_i\le84), and (136\le O_i\le232).

## Remainder bounds and five peels

Assume (n\ge88). Since (q\mid 14n+92), (q\le14n+92\le15X). Also (d\le14n+92). Initially,
[
R_1\ge56(n+6)-232-(14n+92)=42n+12>0.
]
For (i\ge2), (R_i\ge56(n+6)-232=56n+104>0).

Whenever the preceding exponents satisfy (sum_{j<i}t_j\le e), one has (T_i\le2n+6), hence
[
R_i\le84(2n+6)\le200X.
]
The first remainder has the same upper bound. Applying the elementary dyadic remainder-peeling lemma successively to the nested equation gives (A_i\le S_i) and a new quotient (d_i), with
[
S_1=R_1\le200X,quad
S_2=R_2+d_1\le400X,quad
S_3=R_3+d_2\le600X,
]
[
S_4=R_4+d_3\le800X,qquad
S_5=R_5+d_4\le1000X.
]
At the (i)-th peel the scaled remainder is bounded by
[
qA_1\cdots A_{i-1}S_i\le c_iX^{i+1},
]
where
[
c_1=3000,quad c_2=1{,}200{,}000,quad
c_3=720{,}000{,}000,quad
c_4=576{,}000{,}000{,}000,
]
and
[
c_5=15\cdot200\cdot400\cdot600\cdot800\cdot1000
=576{,}000{,}000{,}000{,}000.
]
The fifth bound is the dominant one.

## Sixth-power gap and contradiction

The exact gap
[
576{,}000{,}000{,}000{,}000(n+2)^6<2^n
]
holds for every (n\ge88): check (n=88,89,90,91,92,93), then induct in steps of six using (n+8\le2(n+2)).

After four peels, the terminal equation is
[
K2^{e-t_1-t_2-t_3-t_4}=A_5E+S_5.
]
The fifth peel gives (A_5\le S_5\le1000X). Since (T_6\le2n+6), (E\le2000X), so
[
K2^{e-t_1-t_2-t_3-t_4}
\le S_5(E+1)\le1000X\cdot2001X=2{,}001{,}000X^2.
]
On the other hand, the final coefficient term and (C_5\ge392) give (K\ge392qA_1A_2A_3A_4). Since (qA_1A_2A_3A_4\cdot2^{e-t_1-t_2-t_3-t_4}=2^n), the same quantity is at least (392\cdot2^n). The sixth-power gap implies (2{,}001{,}000X^2<2^n), a contradiction.

## Formalization state

- `FiveLayerGap.lean` contains the (n\ge88) sixth-power gap.
- `FiveLayerBarrier.lean` encodes the five-peel conditional barrier with the sharpened (200X) remainder bounds.
- Both files still need a targeted Lean CI compile. The source coefficient model and a `SourceLowWord` five-shallow lift have not been written.
