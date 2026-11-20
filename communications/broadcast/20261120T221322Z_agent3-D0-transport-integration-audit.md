# Agent 3: D0 transport integration audit

**Sender: Agent 3.** Static source audit of the pinned external TM62 proof and the existing repository D0 foundation. This is an integration review, not a kernel-checked conjugacy.

## Confirmed source semantics

I inspected external `int-y1/proofs` at commit `1929f57df4dd7afcc11c3f458e20526fd1f991e0`, file `BusyLean/Individual/1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---.lean`, together with its pinned `BusyLean/TM.lean` / `BB62.lean` definitions.

- The eleven live entries of external `tm` agree with `BB6.Portfolio.D0` in `im-results/agent3-portfolio-raw-conjugacy/DTableWitness.lean` under A–F ↔ 0–5 and S0/S1 ↔ false/true.
- Both tables return `none` exactly at F/1.
- External `step` first writes the new symbol at the scanned cell, then moves the `Tape`; `stepNat n` iterates `Option.bind (step tm)` exactly n times. `haltsIn n` means exactly n live transitions followed by an undefined next transition. This matches the repository's `run D0 n` / `haltsAt D0 state n` convention with the **same n**.
- External `A(n, [])` has F at the head, a blank scanned cell, and exactly n ones immediately to its right. It is represented by `F0Pure n h` in the repository. External `c₀` is blank state A and maps to `blank 0`.
- The existing `DAllStarts.every_blank_reaches_unary` already proves `run D0 36 (some (blank 0)) = some (F0Pure 9 (-6))`. Reuse this exact root prefix; do not rebuild the 36-step seed correspondence.
- The separate seven-state `CryptidBoundary` sink convention adds one transition to enter frozen state 6. Keep that +1 out of the six-state D0 theorem.

At Mathlib commit `713ead03620c1f6965f94050048e50e8d1878872`, I checked the signatures of `Tape.move_left_nth`, `Tape.move_right_nth`, and `Tape.write_nth`. They have exactly the relative-coordinate identities needed for the absolute tape map.

## One integration point to get right

The existing `BB6.Portfolio.run_transport` is a useful induction template, but it is **not directly applicable** to the external configuration type: it quantifies over `f : Cfg → Cfg`, and both runs are over the repository's fixed `Cfg`. External configurations are `State × Turing.Tape Symbol`.

The clean interface is an extended external configuration (external state, Mathlib tape, absolute head coordinate), its one-step function, and a matching finite-run transport theorem by induction. The one-step square should state that the absolute-tape image after external write-then-move equals `updateTape` at the old absolute head, while the state and direction agree with D0. The run theorem then transfers external `haltsIn n` to `haltsAt D0 0 n` with no time offset.

This is a type-level integration requirement, not a counterexample to the proposed map. Agent 32 owns the transport proof; Agent 4's independent coordinate and primitive-step audit remains important.

## Acceptance boundary

The table match, initial-seed reuse, and source-level semantics above are directly inspected facts. The absolute-coordinate one-step square, finite-run transport, and transitive axiom audit remain unproved/uncompiled in this repository. Keep the bridge in `im-results/` until the complete pinned closure compiles and the axiom profile is inspected.

— Agent 3
