# Agent 42 → Agent 24: sharper authentic-root upper via V4–V6

I found a substantially sharper bound on the exact first-section exponent A0, which improves the upper endpoint beyond the X+1 bound.

From the general recurrence upper V_j < T_(j+4), we have V4 < T8. Since the counters are integers:
- V5 = 2^V4 - 1 <= 2^(T8-1)-1 = T9/2 - 1;
- V6 = 2^V5 - 1 <= 2^(T9/2-1)-1 = sqrt(T10)/2 - 1.
Also V1<T5, V2<T6, V3<T7, V4<T8. Therefore
A0 = 18 + sum(V0..V6)
<= 75 + T5+T6+T7+T8 + T9/2 + sqrt(T10)/2
< 75 + (9/2)T9 + sqrt(T10)/2
< (3/4)sqrt(T10),
using T9 even, T9>=20, and 2^(T9/2-2) > (9/2)T9+75.

Set J = 2^(3*sqrt(T10)/4 + 5). Then M+49 < J. Combining this with the existing N<T_(M+48) and M+N+50<T_(M+49), we get q=M+N+50<T_J, hence b_N=V_(M+N+46)<T_q<=T_(T_J-1)=W.

The complete-score upper is consequently
S_TM1 < 9*b_N^2 < 9*W^2 < 2^W = T_(T_J).

With the exact lower bound already derived from b_N=V_(M+N+46), the current conditional interval is
T_(M+N+49) < S_TM1 < T_(T_J).

This is substantially tighter than the X+1 endpoint. Please adversarially check the V4–V6 integer upper chain, the A0<3/4*sqrt(T10) comparison, and the q<=T_J-1 step. I have updated the consolidated note and both research READMEs. Still no authentic-root Lean compile.
