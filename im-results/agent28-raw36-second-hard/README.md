# Raw36 exceptional one-hole: source-accepted 8-sweep nonhalting proof

**Status: unconditionally proved for every compatible completion, Lean 4.36.0-rc2 (27 November 2026).** This closes the second of two hard one-hole literals left by Agent46's corrected Raw36 two-sided abstraction/sweep bank. It is a *local* `NeverHalts` theorem, not a complete Raw36 parent Cover or a global Busy Beaver bound.

## Literal table and exact universal theorem

```text
1RB0LB_1RC0LA_0RD1RE_0LD1LB_0RF---_1LD0RA
```

The only undefined row is E1. In [Raw36Counter2.lean](Raw36Counter2.lean), `p : PartialMachine` encodes exactly these eleven transitions. The source theorem

```lean
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m
```

holds **for every** possible E1 completion. No special choice of the missing transition is needed, and every table in this 25-completion cylinder is nonhalting.

The proof compiles against the **original** repository definitions of `PartialMachine`, `Machine`, `NeverHalts`, and `run0`, via the independently proved `Agent46AutoPump.check_never` and `SweepPumping` source modules. In particular, it does not merely assume a counter or macro semantics.

## Exact root-sourced parametric growth

Let `Z(m)` denote state **D** scanning the rightmost 0 of the finite tape word

```text
(11100)^m 1100
```

with blank zeros elsewhere. Since `Z0` stores the current cell first and left bits in reverse reading order,

```text
Z(m) = ⟨D, 0011 (00111)^m, ε⟩.
```

The authentic blank run reaches `Z(3)` in exactly **132 primitive steps**. The Lean certificate proves, for *every* natural number `n`:

```text
    run0 p (84*n + 854) (Z(n+3)) = some (Z(n+9)).
```

Equivalently, for every `m >= 3`:

```text
    Z(m) -- (84*m + 602) steps --> Z(m+6).
```

In particular, the exact blank-root return milestones are

```text
    k      m       primitive time      right head       left tape extent
    0      3                 132                8                   -10
    1      9                 986               12                   -36
    2     15               2344               16                   -62
    3     21               4206               20                   -88
    4     27               6572               24                  -114
```

For every `k >= 0`, mathematical induction on the source-checked growth theorem gives a live configuration `Z(3+6k)` at time

```text
    t(k) = 132 + 252*k*k + 602*k,
```

and these times diverge. Thus any compatible complete machine admits arbitrarily long nonhalting blank runs.

## Exact finite certificate and formal acceptance

The source proof uses a **single computable certificate**, accepted by `Auto.check p cert = true := by decide`:

- `family`: state D, left word `0011 (00111)^(n+3)`, right word empty;
- `entry=132`, `increment=6`, affine cost `84*n+854`;
- **8 arbitrary-exponent whole-block transfer actions**, four left costs **19, 15, 15, 15**, four right costs **5, 5, 5, 5**, hence coefficient 84;
- **854 ordinary primitive actions**, bundled into 9 explicit `List.replicate` runs, whose lengths are 18,326,29,104,35,120,40,135,47 and sum to 854.

Each sweep checks its local finite `knownRun` for a *single repeated block*, then uses the source-proved `sweepL` / `sweepR` theorems to transport any number of repeated blocks without inspecting a hidden tail. `Auto.traceRun_sound` composes the eight full sweeps with the primitive steps; its final normalized symbolic zipper is definitionally the family grown by six blocks. Crucially, Lean checks the integer recurrence for **all** n from source soundness, not by sampling n or extrapolating a trace.

Accepted [source CI run 46079464845](https://github.com/FlareZ123/bb6/actions/runs/46079464845):
- Source revision `e0a04b85f07f5ab587c42abeb215a9ffbeddb22d`;
- Source manifest and complete seven-module Lean dependency closure in [artifact 15236094425](https://github.com/FlareZ123/bb6/actions/runs/46079464845/artifacts/15236094425), archive SHA-256 `f44dc771c8d11189a074979c1ee2061e1b07d75946bc886dbe4fe3af7b0677d5`;
- `#print axioms checked`: `[propext]`;
- `#print axioms growth`, `#print axioms never`: `[propext, Quot.sound]`;
- no `sorryAx`, `native_decide`, external oracle, or additional axiom.

The initial CI [46079341215](https://github.com/FlareZ123/bb6/actions/runs/46079341215) correctly rejected a misordered **left-transfer argument** in the untrusted emitter; source fixed before the accepted run. The passed theorem, not the original candidate generator, is authoritative.

## Reproduction and integration

- [find_pump.js](find_pump.js) implements a deterministic symbolic discovery search. `node find_pump.js` rediscovers eight sweep operations and 854 primitive operations, printing the long exact Lean operation list and finite sanity checks. Its search is untrusted.
- [Raw36Counter2.lean](Raw36Counter2.lean) is the fixed, compact four-page source certificate with the 17 alternating blocks of `List.replicate` and sweep actions. The original source checker independently evaluates and validates it.
- [Manual workflow](../../.github/workflows/agent28-raw36-counter2.yml) can be triggered at a pinned source revision. It rebuilds all original Lean dependencies and audits the three displayed theorem axioms.
- Agents 29 and 46 were notified in `communications/`. The exact literal should be substituted into their **corrected** Raw36 open-leaf roster and counted only upon validated source tree integration. No whole-parent bound follows from this single local closure.

The key mathematical advance is a short *machine-specific description* of an arbitrarily long two-sided moving tape transformation, reducible to eight elementary uniform sweeps and a source-accepted fixed-cost growth theorem.
