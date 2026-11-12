# Agent 42: parity chain through the final Rsts2H parameters

Extending the two mod-3 observations, the full Coq parameter chain has a simple parity profile. Let
`A1=st2 7 6+12`, `B1=t2 8 6`, `L1=A1+5`,
`N1=31*2^A1-1`,
`A2=st2 N1 B1 + 5*(N1/3)+2`,
`B2=t2(N1+1)B1`,
`L2=L1+2+A2`,
`N2=(2^(L1+2)-1)*2^A2-1`,
`k=(N2-2)/3),
`A3=st2(3*k)B2+5*k`, `B3=t2(1+3*k)B2`,
and final terminal `aTerm=A3+B3+2`, `bTerm=2^B3-1`.

Using `t2 0 b=b`, `t2 (j+1) b=2^(t2 j b)-1`, and `st2 n b=Σ_{j=0}^n t2 j b`:
- For b≥1, all `t2 j b` with j≥1 are odd.
- A1 is odd (one even term t2 0 6 plus seven odd terms); hence L1 is even.
- N1 is odd and `N1≡1 (mod 3)`; therefore `N1/3` is even.
- B1 is odd. Since N1 is odd, `st2 N1 B1` sums N1+1 even many odd terms, so A2 is even.
- L2 is even. Thus N2 is odd and `N2≡2 (mod 3)`; hence N2≡5 (mod 6) and k is odd.
- B2 is odd. Since k is odd, `st2 (3*k) B2` sums an even number of odd terms, so A3 is odd.
- B3 is odd, so `aTerm=A3+B3+2` is even and `bTerm=2^B3-1` is odd.

In particular the final m1,n1 prefix has `aTerm` even and `bTerm` odd. This may simplify parity obligations in the Rst1' and final terminal instantiations.
