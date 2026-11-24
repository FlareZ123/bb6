# Redundancy of the existing low-modulus filters inside the q0 macro grammar

The exact positive-state residue tests from Agent 6's earlier depth-16 inverse sieve, plus the additional a mod 16 = 9, b mod 8 = 5 exclusion, are encoded as localFilters in Q0LocalFilters.lean. The predicate is an explicit conjunction of the individual residue restrictions; it does not stand for every conceivable root invariant.

**Theorem:** For any two consecutive genuine cone macros (F F F F, F F S F, E F F F or E F S F in forward order), every one of the five states in the later macro satisfies the entire conjunction. This is independent of blank reachability. Even a single macro entails the conjunction at its final three formula rows.

The proof computes each macro row in integer first-counter / total-rank coordinates. For earlier digit e the next shifted coordinates are x=16X+c_e-d_e(R+l_e), r=R+l_e. Substituting these into each row of any later digit d gives affine expressions in X,R. Splitting the 16 ordered digit pairs and five rows proves all congruence implications by Lean omega; no bounded range search or numerical induction hypothesis is involved. Q0LocalTrace.lean proves each integer row equals the actual deterministic accelerator run at that step, with cone and size guards ensuring the natural coordinates are nonnegative. Its theorem two_macro_source_filters transfers the residue result to real prepared-state transitions.

## Consequence

In a sufficiently large exact signed path lift, all complete interior macros that have another macro behind them already satisfy the listed sieve filters. Increasing the number of times these same tests are applied does not introduce independent interior constraints. Any remaining restrictions from them reside at the oldest boundary. This does not preclude a stronger higher-modulus invariant, a different branch grammar, or a global blank-origin argument; nor does it exclude all q0 paths.

Lean 4.36.0-rc2 compiled Q0LocalFilters and Q0LocalTrace against the exact Q0Converse, Q0MacroCore and BB429Rank modules. All exported theorems have only propext, Classical.choice, Quot.sound. No native_decide or sorry. The congruence conjunction is explicitly stated rather than re-importing all of the historical source-certified filter modules; no new assertion of rooted validity beyond the stated algebraic implications is needed.
