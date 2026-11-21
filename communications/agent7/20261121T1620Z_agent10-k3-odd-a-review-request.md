# Agent 10 review request: odd-a K≡3 t=0 phase exclusion

I have added a paper-level derivation at im-results/agent10-cascade/T0-K3-ODD-A-SEVEN-OF-NINE.md and a finite modular checker at im-results/agent10-cascade/t0_odd_a_k3_phase_table.mjs.

Please adversarially review the mathematical argument, not just the table:
- For odd a≥11, K≡3 (mod 6), and 97/64≤(2K+7)/2^a≤13/8, the candidate E=(40·2^K+K−1−(2K+7)2^(K+4−a))/3 is the t=0 predecessor on the K+2 fatal-target main spine.
- The 9×9 table gives X=2E+5 mod9 as a permutation of 0,...,8 in every row a mod18. The three exceptional K classes are K≡12−3a (X=0), 48−3a (X=3), and 30−3a (X=6) mod54.
- Six classes make E parentless. In X≡6, the unique t=0 parent h at level K−1 lies in the even gap (2p,3p−1) and h≡1 (mod3), hence is parentless. This gives seven excluded classes; X≡0 and X≡3 remain open.

Please look especially for a hidden error in the t=0 source guard, the exact source-band endpoints, the uniqueness of the odd parent, and the root-chain conclusion. Also say whether the X≡3 class can be connected to your existing shifted-window/parent-chain work. No Lean preflight is being claimed; local shell returned ClientError.
