# Five-slot finite-support translated nonhalting cylinder

## Result

The partial table `agent27WordPump` fixes exactly five of the twelve state/symbol slots:

| Slot | Transition | Conventional notation |
|---|---|---|
| A/0 | write 1, move right, enter B | 1RB |
| B/0 | write 1, move left, enter C | 1LC |
| C/1 | write 0, move right, enter D | 0RD |
| D/1 | write 1, move right, enter E | 1RE |
| E/0 | write 1, move left, enter C | 1LC |

After the two-step blank entry A/0, B/0, the machine is in state C at head position 0 with the finite set of marked cells exactly `{0,1}`.

The three-step macro is:

| Step | Read slot | Action | State/head afterward | Marked cells afterward |
|---:|---|---|---|---|
| 1 | C/1 | 0RD | D at 1 | `{1}` |
| 2 | D/1 | 1RE | E at 2 | `{1}` |
| 3 | E/0 | 1LC | C at 1 | `{1,2}` |

Thus the complete finite support is translated right by one cell:
`(C, 0, {0,1}) -> (C, 1, {1,2})`.
The exact translated-cycle checker accepts entry length 2 and period 3. Its soundness theorem lifts this finite computation to every total machine compatible with the five-slot table. Repeating the translation gives nonhalting.

The Lean theorem `agent27WordPump_never` states the result directly:
`∀ m, compatible agent27WordPump m → NeverHalts m`.

## Size and relation to the current frontier

There are twelve transition slots and 25 possible outcomes per slot. Five fixed slots leave seven free, so the cylinder contains exactly:

`25^7 = 6,103,515,625` total machines.

Its four-slot parent P4 has mass `25^8 = 152,587,890,625`; this certificate is one of its 25 children.

This candidate is disjoint from:
- the Agent 32 seven-slot sibling, because that table has E/0 = 1LF while this table has E/0 = 1LC;
- the separate two-mark reference cylinder, because that table has C/1 = 1RD while this table has C/1 = 0RD.

The Lean file proves both incompatibilities. It also proves that among all 25 possible E/0 outcomes, this is the unique one-slot P4 extension accepted by the **three-step** translated checker. This is not a claim of uniqueness among longer-period cycles.

## Verification

`TranslatedFiveSlot.lean` was compiled locally with Lean 4.36.0-rc2 after reconstructing the supplied toolchain archive. The exact current-main import closure compiled included:

- `Frontier.lean`
- `Symmetry.lean`
- `RootShift.lean`
- `RayClosed.lean`
- `RayChecker.lean`
- `RayEntry.lean`
- `RayFinite.lean`
- `TranslatedCycle.lean`
- `TranslatedFiniteOracle.lean`
- `FrontierMass.lean`

The candidate's kernel-reduced checker theorem is `agent27WordPump_translated_check`; its all-completions proof is `agent27WordPump_cover`; and the direct nonhalting corollary is `agent27WordPump_never`. Reported axiom profiles are only `propext`, `Classical.choice`, and `Quot.sound` for the translated proof; mass and disjointness proofs use only `propext`. No `sorryAx`, `native_decide`, or custom axiom appears.

The C++ discovery script `search_translated.cpp` performs a deterministic bounded DFS from P4, with macro depth at most 8 and at most five newly assigned slots. It visited 2,398,734 nodes and found 3,428 distinct source tables; the five-slot/three-step candidate above was the smallest cylinder found. The Lean theorem, not the search, is the proof of nonhalting.

## Integration boundary

This file proves a nonhalting cylinder independently of the depth-four audit. It does **not** yet prove that the whole cylinder lies inside `depth4ResidualAudit.open`, nor does it update the interpreted global frontier report. The existing P4 parent-open argument is in `im-results/agent32-zero-prefix-global/SecondWordLeafGraft.lean`, but that module's full dependency closure has not yet passed local preflight. To integrate this stronger child, use the new generic `addCertificate_open_iff` theorem in `im-results/agent8-coverage-contract/IncrementalAudit.lean`, prove the P4-parent corollary, compile the exact full closure, and only then update the global dossier/workflow.

This is a rigorously proved nonhalting family, not a BB(6) upper bound or exact solution.
