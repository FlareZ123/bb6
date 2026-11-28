# Two source-certified 25-completion nonhalting cylinders via 001/010 packet growth

**Agent 38 — 28 November 2026. Full original-source Lean 4.36.0-rc2 acceptance.**

We classify two distinct six-state, two-symbol partial machines, each with exactly one unspecified transition:

| Raw43 B1=0LE / E0=1LA local index | Literal machine (state A through F, underscore-separated) | Unspecified row | Certified source |
|---:|---|---|---|
| **711** | `1RB1RC_1RC0LE_0RD1RF_1LD0RB_1LA1LD_0RD---` | F1 | [M711Proof.lean](../im-results/agent38-raw43-pair/M711Proof.lean) |
| **905** | `1RB1RF_1RC0LE_0RD---_1LD0RB_1LA1LD_0RD1RF` | C1 | [M905Proof.lean](../im-results/agent38-raw43-pair/M905Proof.lean) |

**Result:** Every total completion of either partial table is nonhalting from the standard blank tape. Hence the two disjoint 25-completion cylinders constitute **50 classified complete machines**. Both proofs are original-source Lean theorems `never` and `literal_cover (bound)`, with no unproved premise.

## Shared arithmetic invariant

Use `Z0` near-first zipper notation: `l` includes the scanned symbol. For every `n : Nat`, define

```
word(n)  = 1 (001)^n                  -- right-of-head bit word
phase(n) = ⟨F, 0::11, word(n)⟩
```

The actual blank-tape run reaches `phase(0)` after exactly **10 primitive steps**. For both machines and all `n`,

```lean
theorem growth (n : Nat) :
    run0 table (10*n+18) (phase n) = some (phase (n+1))
```

Every return has strictly positive time. Iterating this identity gives unbounded defined blank-run prefixes, which imply `NeverHalts m` for every total machine `m` compatible with the corresponding partial machine. Neither proof depends on finite cutoff simulation.

## The exact two-stage first return

The **forward stage** uses four literal instructions `F0 D1 B0 C0`, followed by a repeatable three-instruction `D1 B0 C0` which consumes one 001 packet, then an implicit-blank final application. It converts the right word `1(001)^n` into a left-side packet stack and blank right ray in **`3n+4` transitions**.

Define `fshape(n) = 0010 (010)^n 011`. The exact first-stage identity is

```lean
run0 table (3*n+4) (phase n) = some ⟨D,fshape n,[]⟩.
```

The **backward stage** begins with fixed eight-instruction `D0 D0 D1 B1 E0 A0 B1 E1`, which removes the `0010` prefix and creates right packet `1001`. Each of the `n` remaining left-side 010 packets is consumed by a seven-instruction `D0 D1 B1 E0 A0 B1 E1` and prepends right packet 100. A six-instruction finishing path returns to F scanning 0, giving **`7n+14` reset transitions**:

```lean
run0 table (7*n+14) ⟨D,fshape n,[]⟩ = some (phase (n+1)).
```

The arithmetic is `(3n+4)+(7n+14)=10n+18`. No unbounded transition is hidden: the source proves two explicit induction lemmas on the right 001 and left 010 packet counters.

At the final two-instruction part, the machines differ:
- **M711:** A1 = 1RC then C1 = 1RF.
- **M905:** A1 = 1RF then F1 = 1RF.

Both have the same composed two-step effect and identical six-step finish; their missing rows (**F1** for M711, **C1** for M905) are disjoint from the actual orbit. This subtle final-row substitution is why the *same* parametric invariant legitimately solves two different partial-machine cylinders. The equality is established by independent literal Lean compilations, not by a heuristic identification.

## Formal acceptance and scope

- [**M711 original-source Lean run 46086411444**](https://github.com/FlareZ123/bb6/actions/runs/46086411444): success; complete recurrence, `NeverHalts`, any-bound `Cover` source/audit.
- [**M905 original-source Lean run 46086415202**](https://github.com/FlareZ123/bb6/actions/runs/46086415202): success; same theorem structures against its different exact table and different missing row.
- The proof artifacts import `SweepPumping` from the original repository, contain no `sorry`, and invoke the standard `run_project`/ `zrun_sound` bridge from partial to total machines.

Together with the seven earlier Agent38 certificates (M59, M61, M62, M176, M413, M558, M627), this invocation has source-certified **nine distinct one-hole cylinders or 225 complete machines**. This is a substantive **local nonhalting classification** within Raw43, not a proof that Raw43's entire parent, Canonical40, or BB(6) has been resolved.
