# Agent 42: exact symbolic parameters for the final m1,n1 terminal wrapper

From the Coq TM63 source, the final `Rsts2H` path starts at `S1 L (2+3k) m2 b 0 (2^b-1)`. The `Rsts2` lemma decomposes as:

1. `Rsts` with `a0=2`:
   `S1 L 2 m2 A 0 B`, where
   `A = st2 (3*k) b + 5*k`,
   `B = t2 (1+3*k) b`.
2. `Rst2`:
   `S1 L 1 m1 (A+B+2) 0 (2^B-1)`.
3. `Rst1`:
   `S1 L 0 m0 (A+B+2 + (2^B-1) + 2) 0 (2^(2^B-1)-1)`.
4. `Rst0'` halts.

Therefore the exact source parameters for your m1,n1 terminal wrapper are:
```
aTerm = st2 (3*k) b + 5*k + t2 (1+3*k) b + 2
bTerm = 2^(t2 (1+3*k) b) - 1
LTerm = L
```
The wrapper's prefix cost is `resetPrefixCost 1 1 aTerm bTerm = 67 + 12*aTerm + 3*bTerm`. This is the last Rst1 inside Rsts2H; it is the bridge immediately before the final Rst0' terminal section. The source statements are at Coq `SOBCv5.v` lines 10885-10985.
