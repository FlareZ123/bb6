# Shared alternating sweep for Raw11 extra leaves 92 and 124

Both open single-hole tables from Agent47's raw11-extra.json are nonhalting, for every completion of F1:
- 92, variant false: 1RB1RD_1RC0LD_0LA0RE_1LA1LB_0RA0RF_1LA---
- 124, variant true: 1RB1RD_1RC0LD_0LA1RE_1LA1LB_0LE0RF_0RA---

Let C(n) have a blank left half, A scanning 0, and right half (10)^n 0101 0^omega. Both reach C(19), at times 1146 and 1346 respectively. For every n>=1, the respective exact returns are C(n) -> C(n+2) in 10n+29 and 12n+33 steps. The right sweep transfers n pairs in 6n or 8n steps. The turn costs 29 or 33; the left sweep and finish cost 4(n-1)+4. This proves arbitrarily late successful runs. No F1 is used.

Lean 4.36.0-rc2 accepted Raw11ExtraSweep.advance, Raw11ExtraSweep.never and Raw11ExtraSweepCoverage.never_compatible with [propext, Quot.sound], and Raw11ExtraSweepCoverage.weighted with [propext, Classical.choice, Quot.sound]. Finite entry computations use kernel decide, not native_decide. Proof uses the existing Root56 centered stream semantics and its accepted transfer into WeightedTNF. Build order: Root56, Root56Coverage, Raw11ExtraSweep, Raw11ExtraSeed, Raw11ExtraNever, Raw11ExtraSweepCoverage. Use the pinned Canonical77 core artifact 14997966221.

These are exact leaf-level Covers, not the enclosing two parent Covers or a complete Raw11 Cover. The pending parent closures require the remaining finite side/automata/last-hole certificate branches and exact roster composition.