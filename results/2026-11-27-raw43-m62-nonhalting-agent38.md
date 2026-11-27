# A complete regular-language nonhalting proof for a Raw43 six-state one-hole machine

**Agent 38 — 27 November 2026. Original-source Lean 4.36.0-rc2 accepted.**

## Mathematical result

Consider the following six-state, two-symbol partial Turing machine, with the standard blank initial tape and state A:

```
1RB0LA_1RC0LE_0RD1RF_1LD0RB_1LA1RA_0RE---
```

Exactly the state-F/read-1 transition is unspecified. For **every** completion of this entry (the 24 ordinary transitions or the halting transition), the blank-tape run is infinite. Equivalently, the corresponding 25-element one-hole cylinder is entirely nonhalting. The machine is Raw43 B1=0LE, E0=1LA, local index **62**.

The stronger certificate is the universally quantified Lean statement

```lean
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m
theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table
```

The second theorem works for **every** natural bound, since every compatible total machine is nonhalting, and does not presuppose any bound on its execution.

This is a complete **local nonhalting classification**, not an exact value of BB(6), a global upper bound, or a Cover for the enclosing Raw43 parent. The source-level result can be consumed in a later parent Cover construction.

## Closed two-phase tape invariant

At each checkpoint, state F scans zero. Write the finite left tape word in physical left-to-right order as `L` and the finite right tape word beginning at the scanned zero as `R`. All other cells are blank. Define regular frame languages (all displayed parameters are nonnegative; the internal `b_i` satisfy `b_i≥1`):

- `O = {1^(5a): a≥1} ∪ {1^(5a+3)(0 1^(5b_i+1))*0 1^(5c+3)}`.
- `A = {1^(5a+3)(0 1^(5b_i+1))*}`.
- `B = {1^(5a+2)} ∪ {1^(5a+3)(0 1^(5b_i+1))*0 1^(5c): c≥1}`.

A complete left word consists of zero or more O frames separated by `00`, then a terminal A or B frame, likewise separated by `00`. Define right code words `W2(k)=0^(5k+2)101`, `W4(k)=0^(5k+4)101`, and `W=(W2|W4)*`.

**Phase A:** left terminal A, right word either `01` or `01 0^(5k+1)101 W`.

**Phase B:** left terminal B, right word W (including the empty word).

The authentic blank run enters phase A after exactly 12 transitions with left word `111` and right word `01`. A full case distinction on the right language gives positive, defined first-F-return transitions:

| Phase and first right token | Raw cost | Replacement of consumed right prefix | Next phase |
| --- | ---: | --- | --- |
| A, trailing `01` or long 1-mod-5 token | 18 | `010000→110011` | B |
| A, shortest 1-mod-5 token | 8 | `010101→011111` | B |
| B, `W2(0)` | 11 | `00101→11111` | B |
| B, `W4(0)` | 11 | `0000101→1110011` | B |
| B, empty right or long W2/W4 token | positive, unbounded | general backward carry below | A |

The four finite substitutions are literal first-F returns; the B short cases preserve its B terminal frame or create a fresh B frame after closing an O frame. The A cases close its terminal A into O or extend it into B. The B carry consumes its terminal frame and the preceding `00`, leaves three new 1s, and transforms the remaining O stack into a valid A terminal. The resulting right suffix is again exactly the required A code. All possibilities of both right languages are covered.

## Arbitrary-length carry identity

Suppose F scans the first zero after

```
00 1^r1 0 1^r2 0 ... 0 1^rN 00000
```

with `rN≥1`, each preceding `ri≥2`, and arbitrary exterior tape tails. Let `S=Σ ri`. After exactly **`S+18+9N`** primitive transitions, F again scans zero, at head displacement **`2-S-N`**. The displayed interval becomes

```
11101 0^(r1-2)101 ... 0^(r(N-1)-2)101 0^(rN-1)101
```

(for N=1, use `11101 0^(r1-1)101`). The exterior tails are untouched. The literal instruction word factors into fixed 13-, 8- and 3-transition fragments separated by unary A1 sweeps. Lean proves the general arbitrary-length erasure and A-frame scanning lemmas by induction, then composes them into the B-to-A carry for all admissible frames, including the blank exterior case.

The complete induction has strictly positive cost on every checkpoint, and no use of the missing F1 row. It therefore yields arbitrarily long defined partial-machine execution prefixes, which are transported to total-machine `NeverHalts` using the repository's source zipper/run soundness lemmas.

## Formal acceptance and reproducibility

**Final source-acceptance run:** [GitHub Actions 46084476880](https://github.com/FlareZ123/bb6/actions/runs/46084476880), Lean **4.36.0-rc2**, with exactly the repository's original source dependencies. The final run compiled `BB6.Agent38M62.never` and `BB6.Agent38M62.literal_cover`, and completed the standard axiom audit. A predecessor [run 46084386030](https://github.com/FlareZ123/bb6/actions/runs/46084386030) had already accepted the entire `NeverHalts` proof before adding the direct coverage-leaf corollary.

Source files (in dependency order):

1. [M62Core.lean](../im-results/agent38-raw43-pair/M62Core.lean): the exact 11-row table, root entry and four fixed first-return identities.
2. [M62Grammar.lean](../im-results/agent38-raw43-pair/M62Grammar.lean): near-head five-residue O/A/B frame constructors, left-frame conversion, carry tail.
3. [M62Carry.lean](../im-results/agent38-raw43-pair/M62Carry.lean): exact parametric A1 erasures, P/Q/R, and arbitrary-length A-frame scan.
4. [M62Right.lean](../im-results/agent38-raw43-pair/M62Right.lean): W2/W4 and A-code languages, all A-to-B and finite B-to-B returns.
5. [M62B.lean](../im-results/agent38-raw43-pair/M62B.lean): unbounded B-to-A carry across every admissible outer frame stack, including empty tails.
6. [M62Proof.lean](../im-results/agent38-raw43-pair/M62Proof.lean): complete two-phase invariant, unbounded blank-origin prefixes, `NeverHalts`, and the universal `Cover (DecidedBelow bound)` leaf.

The [extended proof derivation](../im-results/agent38-raw43-pair/M62FullNonhaltingProof.md) gives the full case analysis and primitive words. Independent falsification programs [M62CarryMacro.cjs](../im-results/agent38-raw43-pair/M62CarryMacro.cjs) and [M62RegularInvariant.cjs](../im-results/agent38-raw43-pair/M62RegularInvariant.cjs) were executed on 2,293 parametric carries and 32,000 generated invariant configurations respectively, all agreeing with the proof; these tests are supplementary and **not** relied upon by Lean.

The exact BB(6) value remains open, and this result has not yet been consumed by the enclosing Raw43 or Canonical40 covering proofs.
