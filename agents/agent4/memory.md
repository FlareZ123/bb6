# Agent 4 research memory

Normal research mode, claimed 2026-11-02T01:06:47.300Z. The user requested no Critic mode. Work on the existing DeepMind-certified P1/G/T reduction of holdout `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE` (same target agent1 independently studies).

## Preserved mathematical proof

`im-results/agent4-halting-funnel/HaltingFunnel.lean` proves, in Lean 4.36.0-rc2, that every synthetic P1(A_n,0) with A_n=14*2^n-2n-11 halts after exactly 2n+3 calls of the accelerated map (final none included). The theorem `halts_from_zero_exact` and closed-form `A_closed` were compiled with `import Std`, and `#print axioms` contained only [propext, Quot.sound], no sorry. Core inductive stage: (E_j,C(j,n+1))->(E_j+3,C(j,n+1)-2)->(E_(j+1),C(j+1,n)), with E0=2,E_(j+1)=2E_j+12; C(j,0)=4,C(j,n+1)=C(j+1,n)+E_j+10. End state (E_n,4) leads to halting gate.

`im-results/agent4-halting-funnel/README.md` describes exact scope and prior work. `verify_raw.py` independently confirms raw TM halting for n=0,...,8. A separate C++ check (not preserved) checked through n=10. Raw steps for these examples fit (196*4^n-84*2^n-12n-4)/3, derived algebraically from comment costs in DeepMind Lean source; this raw cost formula is **not kernel-checked for all n**. No claim that blank tape reaches this synthetic family; no BB(6) bound.

Empirically 2,000,000 P1 accelerated transitions from actual blank-tape entry (2,1) did not halt, and an odd-parameter scan 1<=a<=5,000,000 showed only 19 family values halt before first leaving the even-c sector. These are finite observations and not mathematical completeness.

## Research next steps

1. Investigate reachable c=0 P1 states and the backwards halting basin; can the family arise from blank tape?
2. Attempt converse classification of **first even-c excursion** for odd c=0 starts and identify possible even-sector resets.
3. Send agent1 the funnel theorem to prevent redundant work, solicit critique and ask whether they see a blank-tape connection.
4. Bridge current independently restated T to DeepMind source only if a consequential blank-tape theorem emerges, otherwise keep as intermediate.

Do not promote to `results/` without frontier-advancing findings.
