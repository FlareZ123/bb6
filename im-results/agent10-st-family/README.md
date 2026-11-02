# Agent 10: second rooted S/T machine enters a common raw S section

**Status (2026-11-02): exact finite raw source theorem with Lean proof (see latest manual CI). Neither rooted holdout is decided. Neither the Busy Beaver value nor an upper bound is established. This is intermediate multi-root proof reuse.**

Two strings in the pinned 2026-10-16 catalogue:

- S: `1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB`.
- T: `1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---`.

## Exact six-state common-table conjugacy

`STableWitness.lean` imports **unmodified** `MachineConjugacy.lean` and `DParseRLE.lean` from Agent 3. It decodes all 12 transition instructions from both *literal strings* and proves every cell of

```
TRoot = renameMachine STPerm (reflectMachine SRoot)
```

where the bijection maps the S state list `(A,B,C,D,E,F)` to T states `(C,A,B,F,D,E)`. Physical tape reflection is part of the conjugacy. Consequently the true rooted T-blank-start A becomes **S-table blank-start B**, not S-table A. Full exact raw-time transports:

```lean
ST_blank_rooted_halts_iff :
  haltsFrom TRoot 0 ↔ haltsFrom SRoot 1
ST_blank_rooted_haltsAt_iff (n : Nat) :
  haltsAt TRoot 0 n ↔ haltsAt SRoot 1 n
```

The original public Cryptids module identifies the two machines as left/right mirrors; it does not by itself license silently equating their *rooted blank starts*. This source-verified mapping records the actual start-state correspondence.

## Newly recovered genuine blank-entry section for T

`SBlankEntry.lean` adapts Agent 3's finite-support simulator to the S table, proves a general finite/raw semantic equivalence on the entire infinite physical tape, and verifies **47 exact raw transitions** from the S-B blank start. At step 47:

- running state B;
- head coordinate 3;
- full set of tape-one coordinates `{-8,-5,-3,-1,1,5,6}`;
- all other tape positions contain zero.

This is precisely the full physical S-section `S0p(0,1,3)` of the published Cryptids source, where `S0p(0,b,c)` has a B-head over blank and physical tape `0^∞ 10(01)^c 01 0^b B>0011 0^∞`.

The exported all-time claims are:

```lean
s_blank_B_47_to_S013 :
  run SRoot 47 (some (blank 1)) = some (S0pZero 1 3 3)
t_blank_A_47_to_S013_halts_iff :
  haltsFrom TRoot 0 ↔ HaltsCfg SRoot (S0pZero 1 3 3)
t_blank_A_47_to_S013_haltsAt_iff (n : Nat) :
  haltsAt TRoot 0 (47+n) ↔ HaltsAtCfg SRoot (S0pZero 1 3 3) n
```

The original S-root blank **A** reaches its **different** section `S0p(0,125,3)` through an upstream Cryptids-certified entry (`T1(0,1)` at 22 raw steps, then seven macro steps). Thus the existing high-level S/T section rules potentially apply to **both rooted starts with distinct input parameters**. In Agent 9's shorthand `q=b+16`, the T-root section has `(q,c)=(17,3)` whereas the S-root section has `(q,c)=(141,3)`. Both entries need to be tracked independently.

The source `S0pZero` uses an explicit infinite-tape Boolean predicate with finite positional support, and its physical interpretation is checked against the published source expression. The Lean module as written does **not** import the separate Google DeepMind Cryptids source module, so the source-to-source `Cfg` representation bridge remains a future desirable certification step.

## Reproduction and boundaries

Manual GitHub workflow: `.github/workflows/agent10-st-conjugacy.yml`. It compiles all Agent 3 source dependencies unchanged, the two literal S/T table theorems, then the exact 47-step physical tape certificate and halting-time transports using Lean **4.36.0-rc2**. The full table conjugacy has already passed [source CI 41465812297](https://github.com/FlareZ123/bb6/actions/runs/41465812297). See the most recent workflow run for the 47-step theorem. All expected final axiom audits must exclude `sorryAx`.

An independent sparse-tape Python simulator found the 47-step section and independently executed T blank A to exactly 47 steps, finding state A, head -3, and tape-one coordinates `{-6,-5,-1,1,3,5,8}`, the reflected S-B configuration. This finite observation motivated the Lean certificate; the certificate is the source of proof status.

**Outstanding problem:** decide whether `S0p(0,1,3)` halts or runs forever, and separately whether `S0p(0,125,3)` halts. Do not infer equal outcomes from the common transition table. Investigate whether Agent 9's proven S/T transfer-cylinder techniques can distinguish the two specific starts. No source-level all-time nonhalting or halting theorem has been produced here.

Author: Agent 10.
