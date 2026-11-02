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

## Second formal result: all-natural even-sector converse (2026-11-02 01:35 UTC)

Created `im-results/agent4-halting-funnel/EvenSector.lean` (imports `HaltingFunnel`; compile base to olean then extension). The kernel-checked theorem `even_trace_from_zero_iff` proves `(∃ steps, EvenHIn steps a 0) ↔ (∃ n, a = C 0 n - 1)`, where `EvenHIn` encodes literal T-halting traces whose second counter is even at every hub. The proof models exhaustive even-sector gates, resets, growth, and exits, includes recursive G parity, and proves `E_j+4≠C(0,m)` for all j,m to eliminate reset-assisted halts. It compiled using Lean 4.36.0-rc2, with axiom audit [propext, Classical.choice, Quot.sound], no sorryAx. README updated. This does not handle later odd-c excursions nor settle blank-tape BB(6).

Next focus: odd-c excursion normal forms and exact constraints on the blank-tape orbit's return to c=0, ideally linking the converse to reachability.


## Major proof milestone (~02:11 UTC): full blank-entry target criterion

Lean module chain `im-results/agent4-halting-funnel/` now also contains:
- `OddReturn.lean`: exact two-/three-step U map for even-a odd-c, unique even-c entry at c=3, clean-halt criterion.
- `GModular.lean` and `Mod8Gateway.lean`: rigorous mod8/mod4 dichotomy and even-k G exit c3 restriction.
- `Reachability.lean`: T from odd c can only produce odd c or c0; no direct transition to positive even c.
- `BlankCriterion.lean`: **full global blank-start reduction** `blank_halts_iff_closed`, proved Lean kernel: (∃s,HaltsIn s 2 1) ↔ (∃n, ReachT 2 1 2 (14*2^n−2*n−10)). This closes Agent1's previously *informal* PHASE-CLASSIFICATION forward direction for all possible odd excursions, using strong induction on halting trace length plus EvenSector complete converse. Axioms [propext, Classical.choice, Quot.sound], no sorryAx.
- `BlankInvariants.lean`: `blank_even_left_invariant` proves all reachable positive-c even-a hubs satisfy a=2 or a%4=0. `BlankReach` forward-path form is proved equivalent to `ReachT 2 1`.
- `NoFirstTarget.lean`: `blank_ne_first_critical : ¬BlankReach 2 4`. Verified permanent nonreachability by exhaustive predecessors (2,4) ← (3,0) ← (1,1) or (0,2), last two no T predecessors.
- `NoSecondTarget.lean`: `blank_ne_second_critical : ¬BlankReach 2 16`. Backward: (2,16) ← (15,0) ← (13,1) or (12,2). The (13,1) branch requires forbidden (10,3), contradicting blank_even_left_invariant. The (12,2) branch requires (3,10) ← (0,12), which has no predecessor under T. Rigorous `G_even_positive_output_direct` handles all recursion. Entire proof compiled Lean 4.36.0-rc2 with standard axioms only.
All files committed to main and README synthesized. Broadcast `communications/broadcast/2026-11-02T0157Z_agent4-formal-global-criterion.md` and direct note to Agent1 `communications/agent1/2026-11-02T0207Z_agent4-global-criterion-verified.md` publicized criterion and first exclusion.

**Interpretation:** Real original blank-tape equivalence still depends on DeepMind published machine-to-T certificate, not locally imported. All arithmetic proof theorems fully kernel checked in independent restatement. Excluding n=0,1 is a genuine all-time blank-entry property but does not classify the holdout or improve BB(6) bounds. The next unresolved target is n=2 with c=42; attempt symbolic generalized backward predecessor certificates or a finite automaton invariant to exclude all n, and avoid redundancy with Agents1/5.

**Time/lease:** original claim 2026-11-02T01:06:47.300Z. At checkpoint get actual runtime clock. Do not release before elapsed >=70min, then final cleanup, commit, verify, delete lease as the LAST repository mutation, verify.


## Last substantive advance (~02:13 UTC)

`im-results/agent4-halting-funnel/ThirdTarget.lean` contains kernel-checked theorem `third_critical_iff_gateway : BlankReach 2 42 ↔ BlankReach 36 3`. Derivation: unique predecessor (2,42)<-(41,0), then (39,1) or (38,2). The latter is forbidden by `blank_even_left_invariant`; (39,1) has only predecessor (36,3). Conversely (36,3)->(39,1)->(41,0)->(2,42) directly. Axiom audit [propext,Classical.choice,Quot.sound], no sorryAx. Since n0/1 are excluded, **(36,3)** is the first as-yet-unresolved odd-counter gateway feeding the remaining critical set. No claim it is globally unreachable. README updated.

All mathematical work preserved under `im-results/agent4-halting-funnel/` due restricted scope; results/ unchanged. Critical next step for future incarnation: prove ¬BlankReach 36 3 or find a genuine witness, then tackle general n via finite/symbolic predecessor closure; import Google DeepMind original certified T bridge for decisive theorem. Avoid speculative infinite nonhalting based on finite orbit samples.
