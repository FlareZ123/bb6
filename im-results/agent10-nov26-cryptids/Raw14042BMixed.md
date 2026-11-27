# Mixed B-terminal bank (sibling 42)

The new Raw14042BMixed.lean proves the following recurrence on the common nine-row partial table. Write Q(a,b,n,X,s)=ER(1X,1^a5 2^b (322)^n s), with b>=2, and s in the C-tail six-cycle. Then

    Q(a,b,n,55X,s) -> Q(a+1,b+1,n+carry(s),X,next(s)).

The theorem pairs iterates k rounds, consuming exactly 2k fives, increasing both a and b by k, and adding the C-cycle carry count. The two halves are independent framed computations:
1. Scan a ones and the marker 5 into the left bank; the local 22-step bridge changes ER(11Z,22Y) to EL(3Z,123Y). Sweep a+1 threes and consume a 5, reaching ER(1X,1^(a+2)23 2^(b-2)Y).
2. Scan those ones, then the 11-step bridge ER(1Z,23Y)->ER(25Z,3Y). Apply scanTwo, scanTrip, prep and backAll. The local six-step bridge BL(53Z,Y)->EL(Z,52Y) restores the marker, and the sweep consumes the second 5.

Reproduce: generate Raw14042BMixedLocal.lean with generate_raw140_42_bmixed.py in the directory containing generate_raw140_42_mixed.py. Compile using the same Raw14042Counter/Raw140ERSweep closure as the mixed A bank. Local Lean 4.36.0-rc2 accepted both pair and pairs, axiom list [propext, Quot.sound].

Paper-level application: B-terminal 62542 at exponent p even seeds ER(13 5^(p-3),1123315), then reaches Q(2,3,0,5^(p-4),325). Apply (p-4)/2 rounds. The depletion after the last 5 remains unresolved; no sibling Cover or universal BB(6) bound is claimed.
