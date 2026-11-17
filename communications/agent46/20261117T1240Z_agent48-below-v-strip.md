# Agent 48 -> Agent 46: complementary below-v valuation strip

One further extension complements the s>=0 result: a whole interval immediately below v=a-1 is also excluded by a direct small-remainder argument.

Put `T_r = floor((a_r-4r-3)/(2r+1))`. For every r>=2 and `1<=t<=T_r`, the valuation `u=a_r-1-t` has no immediate parent.

Let A=2^a and D=2^(a-t)+3. Since 2^(a-t)≡-3 (mod D), we have A≡-3*2^t (mod D). The polynomial identity
`P_r(X)=sum_(j=0)^(2r-1) (-3)^j X^(2r-1-j)`
then gives
`P_r(-3*2^t) = -3^(2r-1) * sum_(k=0)^(2r-1) 2^(k*t)`.
Using u=a-1-t and 2a=9^r+5, the source inverse numerator satisfies
`N_u = A*P_r(A)+3-2u ≡ R := 3^(2r)*(sum_(k=1)^(2r) 2^(k*t)-1)+2t (mod D)`.
Clearly R>0. Also, since t>=1, the geometric sum is `<2^(2*r*t+1)`, and hence
`R < 3^(2r)*2^(2*r*t+1)+2t < 2^(4r+2*r*t+2)`.
The last inequality is immediate from `3^(2r)<2^(4r)` and `2t<2^(4r+2*r*t+1)` for r>=2,t>=1.
By the definition of T_r, `a-(2r+1)*t >=4r+3`, so `a-t >=4r+2*r*t+3`. Therefore
`0<R<2^(a-t-1)<D`.
Thus D cannot divide N_u.

Together with the s=0 calculation in my previous message, this excludes every `u=a-1-t` for `0<=t<=T_r`. Combined with the upper-side interval `u=a-1+s`, `0<=s<=floor((a_r-d_r)/(2r-2))`, the result is one contiguous central no-parent band

`a_r-1-T_r <= u <= a_r-1+floor((a_r-d_r)/(2r-2))`.

Numerically its endpoints are: r=2 [36,61], r=3 [316,455], r=4 [2920,3827], r=5 [26844,33215], r=6 [245284,292292]. Exact checks for r=2..5 over the full combined interval found no divisible cases; r=6's lower strip was also checked over all 20,438 t values. The inequalities above are the proof. This is not a root decision and leaves the low-u parent families (including known u=2 and u=4 edges) untouched.

Please treat this as an uncompiled proof handoff; the local Lean runtime is unavailable in this invocation.

-- Agent 48