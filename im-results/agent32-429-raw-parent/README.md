# BB429 original-machine F-entry barrier and remaining C/0 fatal predecessor

**Status: original-source kernel-checked, 7 November 2026.** The genuine blank-start six-state machine `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA` remains undecided. This dossier proves one all-time raw-tape predecessor exclusion and records the surviving local gate. It does not prove halt or nonhalt, improve BB(6) bounds, or establish external novelty.

## Mathematical theorem

Let `M` be the exact six-state machine encoded by Agent1's [authenticated physical frontier](../agent1-429-physical-frontier/BB429PhysicalFrontier.lean). A configuration consists of state, integer head position and the actual two-way infinite Boolean tape. Write `run M n blank = some c` for `n` successful raw transitions.

1. **F-entry invariant.** At every authentic blank-root time `n`, if the head is in state F, the cell immediately to its right is zero: `c.state = F → c.tape (c.head+1) = false`. There is exactly one incoming transition to F, `A/1 = 0LF`, which erases the departure cell and leaves it directly to F's right. The initial state A differs from F. This is an induction-free one-step predecessor argument covering every `n` by splitting off the final transition.
2. **F/0-to-D safety.** If such an F configuration reads zero, the actual rule `F/0 = 1RD` moves into D over that same guaranteed-zero cell. Thus **this route cannot reach D scanning one**, at any time.
3. **Necessary fatal predecessor.** The only transitions into D are `C/0 = 0RD` and `F/0 = 1RD`. Combining the exact table inspection with item 2, any reachable configuration in D scanning one at time `n+1` has a predecessor in C scanning zero at time `n`. This is [`target429_D1_only_from_C0`](BB429FEntry.lean). Since D/1 is the machine's only halting row, any actual halt must pass through this C/0 predecessor.

These claims use **actual infinite-tape semantics** from `BB6Coverage.Frontier`, with no simulated-history length bound, guessed read-zero path or synthetic start. The general lemma `safe_F` applies to any machine with the same destination-F write-zero-left property and a distinct initial state A.

## Original-source verification

[Lean proof](BB429FEntry.lean) imports the unmodified Agent1 `BB429PhysicalFrontier`, reuses its literal twelve-row `target429`, and inspects its actual rows, rather than a separately reconstructed table. Local development first compiled with Lean 4.36.0-rc2 against a signature-identical stand-in for the imported source definitions. Final original-source [manual CI run 42320830215](https://github.com/FlareZ123/bb6/actions/runs/42320830215) **succeeded** at commit `c5a5634bd1b1e43ea4b0ff9c8db547ec038e3319`. Its workflow [agent32-429-raw-parent.yml](../../.github/workflows/agent32-429-raw-parent.yml) builds the original BB6Coverage dependency graph, the Agent1 rooted physical frontier and this source module under Lean 4.36.0-rc2, with `#print axioms` and a `sorryAx` rejection. Source code uses no `sorry`. Locally the corresponding proof showed standard axioms `[propext, Quot.sound]`.

## Scope, relation to existing work, and next decisive proof

This small source-exact raw predecessor fact is complementary to Agent6's original Cryptids accelerator [44/1024 necessary terminal mask](../agent6-harmonic429/README.md) and Agent1's [673 affine inverse certificates](../agent1-429-262144-sieve/README.md). The present lemma is a direct raw control-flow and tape-write restriction, and may already be implicit in the published acceleration; no claim of priority is made. It is retained in `im-results/` as intermediate research.

The **surviving unsolved route** is `B/0 = 1RC`, `C/0 = 0RD`, then D/1. Immediately before the B/0 step, the local scanned cells at B and the two cells to its right must be `0,0,1` for a fatal C/0-to-D/1 sequence. Prove that this local event is impossible on every authentic blank-root configuration (which would decide #429 nonhalting), or exhibit a genuine reachable witness. Finite raw traces and bounded head-neighborhood abstractions are insufficient by themselves. Source-level coupling to the existing accelerated inverse grammar is a better next test than extending simple modular masks.

No `results/` promotion is warranted without a genuine frontier advance beyond these necessary prerequisites.
