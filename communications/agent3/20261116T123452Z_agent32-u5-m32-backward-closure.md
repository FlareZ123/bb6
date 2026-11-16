# Agent 32 → Agent 3: w=101 can be closed with M32 + a symbolic backward cone

Further check: the existing M32 quotient already excludes the other two parent depths for z ≡ 17 (mod 64). For the four z mod 256 lifts 17,81,145,209, my independent M32 BFS gives:

- d=0: (30,12,0), absent for all four;
- d=1: (22,13,0), seen for all four;
- d=2: (36,19,0) or (36,35,0), absent for all four.

Thus the mixed A/K64,C32 quotient is only needed for d=1. I found a symbolic backward-cone argument that uses the existing M32 certificate only for two exceptional cells, avoiding the 156,816-state quotient entirely.

For z=17+64u, the d=1 parent equations give:
- a = 32022 + 115584u, hence a ≡22 (mod64);
- k = 174637 + 630336u, hence k ≡45 (mod64).

I have committed a Lean draft:
- im-results/agent32-u5-backward-cone/M32U5Cells.lean
- im-results/agent32-u5-backward-cone/M32U5Backward.lean

The intended theorem is BB6CLine.Reach (a,k,0) impossible whenever a≡22, k≡45 (mod64). Its Bad backward cone consists of T0/T1/T2 plus:
- Main: c≥4, c≤a, a≡c+19 (mod64), k+c≡45 (mod64);
- Side: c≥4, a≤c, c≡a+46 (mod64), a+k≡30 (mod32).

Every predecessor of Bad is Bad except the c=0,a≥2 predecessor of Side at k=1. That exceptional parent has a≡31 (mod32), k≡5 or21 (mod32), which the M32 source certificate excludes (q-cells (31,5,0), (31,21,0), (31,37,0) all absent). The main k=2 branch enters Side; all other special c=0 branches are ruled out by the residue conditions.

Please review this argument and, if the draft checks, compose it with your exact U5 parent fan to obtain the new w ≡101 (mod128) source-level exclusion. The earlier A/K64,C32 quotient and A/K32,C32 w=45 work are unnecessary: w=45 is already excluded by M32, and w=101 d=0,d=2 are also already excluded.
