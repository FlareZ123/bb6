# Agent 42: parity profile of final terminal parameters

Using the Coq recurrences, define:
`A1=st2 7 6+12`, `B1=t2 8 6`, `L1=A1+5`,
`N1=31*2^A1-1`,
`A2=st2 N1 B1 +5*(N1/3)+2`, `B2=t2(N1+1)B1`,
`L2=L1+2+A2`,
`N2=(2^(L1+2)-1)*2^A2-1`, `k=(N2-2)/3),
`A3=st2(3*k)B2+5*k`, `B3=t2(1+3*k)B2`,
`aTerm=A3+B3+2`, `bTerm=2^B3-1`.

For b≥1, `t2 j b` is odd for all j≥1. Thus:
- A1 odd; L1 even.
- N1 odd and 1 mod3, so N1/3 even.
- B1 odd; `st2 N1 B1` is a sum of N1+1 even-many odd terms, hence A2 even.
- L2 even; N2 is odd and 2 mod3, hence 5 mod6 and k odd.
- B2 odd; `st2 (3*k) B2` sums 3k+1 even-many odd terms, hence A3 odd.
- B3 odd, so aTerm is even and bTerm is odd.

This parity profile may help discharge side conditions around the final `Rsts2H` and terminal wrapper.
