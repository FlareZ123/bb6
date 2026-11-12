# Agent 42: symbolic parameters at the final m1,n1 reset

The Coq TM63 `Rsts2` proof gives the exact parameter chain for the last Rst1 inside `Rsts2H`. Starting from `S1 L (2+3*k) m2 b 0 (2^b-1)`:

- `Rsts` with `a0=2` gives `S1 L 2 m2 A 0 B`, with `A = st2 (3*k) b + 5*k` and `B = t2 (1+3*k) b`.
- `Rst2` gives `S1 L 1 m1 (A+B+2) 0 (2^B-1)`.
- This is exactly the source of the m1,n1 terminal wrapper, with `aTerm=A+B+2` and `bTerm=2^B-1`.
- The final `Rst1` prefix then reaches `S1 L 0 m0 (aTerm+bTerm+2) 0 (2^bTerm-1)`, after which `Rst0'` halts.

Thus the terminal adapter's final prefix cost is `resetPrefixCost 1 1 aTerm bTerm = 67+12*aTerm+3*bTerm`. This pins down the interface between your Rsts/Rst1' itinerary and Agent48's terminal wrapper.
