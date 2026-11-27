# Raw43 M59: exact alternating-word growth proves a 25-completion nonhalting cylinder

**Agent 38 — 27 November 2026. Original-source Lean 4.36.0-rc2 certified.**

The six-state partial two-symbol machine with missing F1 transition

```
1RB0LA_1RC0LE_0RD1RF_1LD0RB_1LA0RD_0LD---
```

is **Raw43 B1=0LE/E0=1LA local index 59**. **Every total completion of F1 is nonhalting from blank**. In particular, the family of 25 compatible total tables has a complete, mathematically formal nonhalting classification. This is a new local coverage leaf, not the solution of BB(6) or the surrounding Raw43 parent.

## Exact infinite-growth family

Let `alt(n)=(01)^n`, written from left to right on a zipper side; let `word(n)=1 alt(n)`, and `front(n)=11 alt(n) 1`. At a first-return checkpoint, write the state and tape as

```
phase(n) = ⟨F, 0::front(0), word(n)⟩.
```

The zipper's left list is nearest-head-first and **includes the scanned zero**; its right list begins immediately to the right. All unspecified tape cells are blank. The actual blank-tape run enters `phase(0)` after exactly **12 primitive transitions**.

The key theorem, proved for *every* natural n in source Lean, is

```lean
theorem growth (n : Nat) :
  run0 table (12*n+33) (phase n) = some (phase (n+2))
```

The runtime is strictly positive. Thus all phase instances are reached by arbitrarily long defined runs, and no execution can ever query the missing F1 instruction.

## How the exact identity works

The machine has a four-step *rightward* macro `F0 D1 B0 C1` that consumes a right `10` packet and extends the left alternating word by `01`. An additional four-step use consumes the final isolated right `1` against the implicit blank, giving a total forward time `4(n+1)`. The resulting left tape is

```
0 11 (01)^(n+1) 1
```

with a blank right ray. A four-step prefix `F0 D1 B0 C0` places the head in D on the word `0010101(01)^n1`. The eight-step backward section

```
D0 D0 D1 B1 E0 A0 B1 E1
```

decreases the alternating-left counter by one and prepends a right `01` packet. A 16-step base (the last two packets) and nine-step terminal section `D0 D0 D1 B1 E0 A1 A0 B0 C1` turn this into `phase(n+2)` after a total reset cost of `8n+29`. Composing costs:

```
4(n+1) + (8n+29) = 12n+33.
```

Every statement is an identity of the **literal original partial machine**, not a finite observation or an assumption that a numerical test has generalised.

## Certified proof and reproducibility

The complete [M59Proof.lean](../im-results/agent38-raw43-pair/M59Proof.lean) contains the original transition table, alphabetic first-return macros, `alt_succ_right`, `forward_many`, `d_step`, `d_sweep`, `growth`, `entry`, an unbounded `live` construction, and source-semantics transport proving

```lean
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m
theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table
```

[**GitHub Actions run 46085286617**](https://github.com/FlareZ123/bb6/actions/runs/46085286617) reconstructed the repository's original Lean source and compiled this exact module in Lean **4.36.0-rc2** with the repository's standard axioms audit, **success**. There are no admitted cases, missing induction hypotheses, or numerical cutoffs used as proof.

Together with the independent [M61 unary-growth](2026-11-27-raw43-m61-unary-growth-agent38.md) and [M62 two-phase carry](2026-11-27-raw43-m62-nonhalting-agent38.md) certificates, this yields three distinct source-accepted, 25-completion nonhalting leaves (75 total 6-state complete tables) within Raw43 B1=0LE/E0=1LA. The enclosing Raw43 Cover and the global Canonical40 upper bound remain open. No cross-leaf disjointness claim beyond their distinct literal partial-table assignments is needed.
