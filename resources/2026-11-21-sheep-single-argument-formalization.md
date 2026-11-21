# Sheep single-argument formalization

**Retrieved:** 2026-11-21  
**Machine:** `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`  
**Primary source:** [rwst/bbchallenge — `machine.lean`](https://github.com/rwst/bbchallenge/blob/main/1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE/machine.lean)  
**Pinned Git blob:** `77ec9bec576a93aff38c483e8345561a14905c1b`  
**Related explanation:** [BusyBeaverWiki machine page](https://wiki.bbchallenge.org/wiki/1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE)

## What the Lean file proves

The 1,353-line Lean module in `rwst/bbchallenge` defines the exact six-state machine and a macro configuration `A(m,n)`. It proves the macro transition rules, the halt cases, the initial configuration reach, and a correspondence with a one-argument arithmetic iterator. Its final theorem is:

```lean
theorem tm_halts_iff_exists :
  (∃ k, (run tm (initConfig 6) k).state = none) ↔
  ∃ n : ℕ, fAIter n (some 5) = none
```

The iterator starts at `5`. Its step function is defined by writing `b=2^k*u` with `u` odd and `a=(u-1)/2`:

```lean
noncomputable def fA (b : ℕ) : Option ℕ :=
  if b = 0 then none
  else
    let k := ord2 b
    let odd := b / 2^k
    let a := (odd - 1) / 2
    if a = 0 then none
    else if a = 1 then some (b + k + 3)
    else some (b + k + a)
```

Equivalently:
- odd part (u=1): halt;
- odd part (u=3): next value (b+v_2(b)+3);
- odd part (u\ge5): next value (b+v_2(b)+(u-1)/2).

This is the same single-argument recurrence described on the BusyBeaverWiki page. The Lean theorem is a **halting equivalence**, not a nonhalting proof: it reduces the original BB(6) question to whether the orbit of (5) under `fA` ever reaches `none`.

## Relationship to this repository's Sheep work

Agent 16's `EvenSourceBridge.raw_halts_iff_even_power` is another source-level reduction for this same machine, using `SheepEven.EvenReach` and powers of two. The `fA` representation and `EvenReach` representation are therefore two independent routes from the same raw machine. No pointwise simulation or conjugacy between the two arithmetic dynamics has yet been recorded here. Establishing that bridge could let the 1458-family inverse-tree results be translated into direct statements about the simpler `fA) orbit, or provide an independent way to attack the unresolved orbit.

## Trust and scope

- The module imports `BusyLean` and Mathlib, so it is not a drop-in file for this repository without its dependency setup.
- The file's summary explicitly describes the proof chain as sorry-free. A lexical scan found no `admit`, `axiom`, or `unsafe`; the only occurrence of the word `sorry` is in a stale comment near the macro-rule section (`all sorried`), not a proof term.
- The page's later “Analysis by Aristotle” gives useful candidate lemmas about immediate predecessors of powers of two, but those comments are not part of the cited Lean theorem and should be independently proved before use.
- Nothing in this formalization determines whether the orbit from (5) halts. The BB(6) holdout remains unresolved.
