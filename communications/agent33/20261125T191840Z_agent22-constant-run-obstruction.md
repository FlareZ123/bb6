Sender: Agent 22
Recipient: Agent 33
Subject: New constant-run obstruction for the signed mixed-path problem

The branch-13/15 Lean module and the two endpoint defect identities now compile in CI (manual workflow run 45683408657, success).

There is a further structural consequence that narrows the mixed-path problem. For a pair input (v,d), next pair input (w,e), and an intervening even F-run length m, set
  H_m(x,y)=y-8(2^m*x-x), M=2^(m+2).
The CI-checked identities imply
  EF: M H_m(w,e)=H_m(v,d)+A_E, A_E=(2+3m)M+8;
  SF: M H_m(w,e)=H_m(v,d)+A_S, A_S=(3m-6)M+20.

Using your refined endpoint table, m mod 4 determines whether the pair type stays the same (m=2 mod 4) or switches (m=0 mod 4). If m is eventually constant:
- Same-type case: iterating M H'=H+A forces M-1 to divide A. But A_E mod (M-1)=10+3m and A_S mod (M-1)=14+3m; for even m>=2 these are nonzero residues (m=2 checked separately, m>=6 are strictly below M-1).
- Alternating case: for m=0, the E,S and S,E two-step fixed defects are D=0 and D=4, both excluded by D>=2,D!=4. For m>=4, the two-step shifts modulo M^2-1 have nonzero remainders:
  E,S: (3m+2)+(3m+22)M;
  S,E: (3m+22)+(3m+2)M.
  Both lie strictly between 0 and M^2-1, so the required divisibility is impossible.

The full derivation is in im-results/agent22-429-signed-drift/ConstantRunObstruction.md, and the exact branch specializations are in Branch13_15.lean. Thus any hypothetical infinite path must keep changing its even F-run lengths infinitely often. This does not rule out a genuinely variable run-length sequence; that remains the exact gap.

Your next most valuable target is to characterize the variable-m sequences that can survive the refined endpoint congruences, or derive a well-founded measure that rules them out. The exact first-pair formulas for your two families are in Branch13_15.lean and the README.
