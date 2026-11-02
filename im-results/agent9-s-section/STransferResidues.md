# Exact immediate T-phase halting residues of the published cryptid_9 S/T accelerator

Agent 9, 2026-11-02. **Standalone Lean-verified, source-derived all-natural necessary-and-sufficient criterion for immediate high-level T halting. Intermediate mathematical reduction, not an original blank-machine halting decision or BB(6) upper bound.**

## The source transition being analyzed

Pinned DeepMind Cryptids source revision `c86f15861709b76042998c5211c7b2f83991621b`, module `BusyBeaver/BB6/M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.lean`, defines `highLevelNext` on `HighLevelState`. Its `T(m)` branch contains up to four nested quotient sweeps. The arithmetic map of each of its first three stages is `g(m)=4*(m/3)+7`. The fourth gate uses `g4(m)=4*(g^3(m)/3)+6`. Each branch has one of six mutually exclusive outcomes: Tn, S, T, Eb, Ed, or `none` for immediate macro halting.

The standalone [`STTransferResidues.lean`](./STTransferResidues.lean) defines `tTag m` with numerical tags 0=Tn, 1=S, 2=T, 3=Eb, 4=Ed, 5=immediate high-level halt. Its literal conditional tree matches the published T source branch, without importing the full original machine module.

## Exact all-natural theorem

```
BB6.Agent9STResidues.immediate_halt_seven_residues (m : Nat) :
    tTag m = 5 ↔
    m%243=10 ∨ m%243=37 ∨ m%243=64 ∨ m%243=91 ∨
    m%243=145 ∨ m%243=172 ∨ m%243=226
```

These are exactly seven classes modulo 243 for **a halt on the next T high-level transition**. An input in any other class may still halt after later T or S transitions. The theorem therefore classifies the direct T gate, not the entire long-term T orbit.

The proof is all-natural: integer arithmetic establishes `g(243*k+r)=324*k+g(r)`, `g²(243*k+r)=432*k+g²(r)`, `g³(243*k+r)=576*k+g³(r)`, and `g4(243*k+r)=768*k+g4(r)`. Each coefficient is divisible by 3, so all branch conditions have period 243. A kernel-computed finite `Fin 243` check then gives the exact seven-class list. It is a mathematical equivalence for every m, with no finite simulation horizon.

## Direct S-to-T-to-halt gateway

The published original S-section S(b,c) has transfer to T exactly when `b%3=2` and `c=0` and then transfers to the T counter `m=4*(b/3)+7`. Define q=b+16, as in prior Agent9 S arithmetic. The exact relation certified in [`STransferTarget.lean`](./STransferTarget.lean) is

```
q%3=0,  c=0,  m+17=f(q),
```

where `f(q)=4*(q/3)` on this branch. Composition with the T residue theorem yields the following **necessary-and-sufficient immediate-next-T-halt criterion conditional on the S transfer**:

```
BB6.Agent9STransferGate.transfer_immediate_halt_iff (b c m : Nat)
  (h : sourceSResult b c = .inr m) :
    immediateHalt m ↔
    (b+16)%729=0 ∨ (b+16)%729=81 ∨ (b+16)%729=243 ∨
    (b+16)%729=324 ∨ (b+16)%729=405 ∨
    (b+16)%729=486 ∨ (b+16)%729=567
```

Thus exactly seven q residue classes modulo 729 encode a direct S-transfer followed by immediate high-level T halting, provided that the separate c-height transfer guard has been met. These seven classes all have q divisible by 3. This theorem does not classify any later return to S or T and does not show either actual rooted q=17 or q=141 trajectory reaches one of the gates.

## Certification and reproduction

All three files `STransferTarget.lean`, `STTransferResidues.lean`, and `STransferGate.lean` compiled locally under Lean 4.36.0-rc2. Final axiom audits:

- `transfer_q`: `[propext, Classical.choice, Quot.sound]`
- `immediate_halt_seven_residues`: `[propext, Quot.sound]`
- `transfer_immediate_halt_iff`: `[propext, Classical.choice, Quot.sound]`

No `sorryAx`, declared axioms, or mock imported lemmas. The code uses only the core Lean and Std libraries plus previously committed S-section arithmetic modules. To match the original high-level `T` branch it restates the published nested divisions, with literal case order. The exact original unmodified Cryptids `HighLevelState` module has **not** been imported and checked in the same kernel environment. An end-to-end original-source bridge to the designated blank-start machine is therefore an outstanding provenance task.

The residue theorem is elementary modular analysis of already published acceleration, not an asserted novel blank-tape machine decision. Retain under `im-results/` until combined with an actual rooted reachability or nonreachability result. The open frontier remains a deterministic all-time proof of the actual S root starting at q=17 or q=141, and ultimately universal six-state halting completeness.
