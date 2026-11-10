# Exact physical TM63 tape-sweep costs

**Result and status.** For the exact published six-state, two-symbol TM63 transition table `1RB---_1LC0RF_1RE0LD_0LC1RB_1RA1RE_1RE0RD`, a fully explicit infinite-tape Lean model proves two arbitrary-length primitive-step identities. The source table is copied literally into `BubbleSource.lean`, with a total tape `Int → Bool`. The statements are kernel checked locally in Lean 4.36.0-rc2, with axiom audits restricted to `propext` and `Quot.sound`. They are **machine-specific quantified lemmas**, but have not yet been imported as theorems about the unchanged repository `BB6Coverage.Agent48Champion.tm2` definition. They do **not** prove an exact TM63 champion runtime or determine BB(6).

**Leftward zero crossing.** If state D reads a one at position `h`, the next cell to the right is zero, and the `n+1` cells ending at `h` and extending left are ones, exactly `3(n+1)` successful TM63 steps put the machine back in state D with head `h-(n+1)`. Its tape differs from the original only at the entering right cell `h+1` (changed to one) and the leftmost crossed cell `h-n` (changed to zero). This is `bubble_run_closed`; the three-step induction kernel is `bubble3`. No conditions are imposed on other tape positions.

**Rightward triple conversion.** If state D reads an uninterrupted run of `3n` ones from its head, exactly `3n` successful source steps put it in state D, `3n` cells to the right, with the complete tape given by `tripleTape n`. Each three-cell segment of ones is converted to the source action's `100` pattern. This is `triple_run`; its three-step kernel is `triple3`. The remainder of the bi-infinite tape is arbitrary.

These two sweep laws identify the repeatable micro-operations observed in the still-unproved all-parameter terminal macro
```text
TM63 S1(L,0,m0,a,0,b) → halt query after 59 + 12*(L+a) successful steps.
```
For a true terminal theorem, define the actual `S1` tape inside Lean and compose the sweep lemmas with the intervening bounded raw actions. In the tested configurations the path contains a three-step-per-cell leftward scan over `5+3L` ones, a repeated rightward triple conversion of length `3L`, then another of length `3a`. The remaining actions are fixed-length connectors. The phase decomposition is **finite computational evidence**, so it is not asserted as a universal theorem.

## Verification and reproducibility

- [BubbleSource.lean](BubbleSource.lean): defines the complete exact TM63 action table; source-small-step `step`, `run`, `run_add`; both all-natural sweep statements and full-tape postconditions.
- Version: Lean `4.36.0-rc2`, import only `Lean`, command `lean BubbleSource.lean`. Locally `#print axioms` for `bubble3`, `bubble_run`, `bubble_run_closed`, `triple3`, and `triple_run` reports only standard `propext`, `Quot.sound`; no `sorry` is used.
- Exact reference table and publication context: [Agent 48's source-connected table](../agent48-champion-root/ChampionRootBridge.lean) and [Agent 24's counted-macro dossier](../agent24-champion-time/README.md), including the tested terminal formula and the full symbolic champion score candidate.

**Open obligations.** A source-level semantic bridge from `ChampionBubble.action` to `BB6Coverage.Agent48Champion.tm2`; an all-parameter counted terminal `S1` theorem; counted increment/reset macros; source-connected composition with the symbolic champion itinerary; and the separate global upper bound for BB(6). The current result supplies reusable all-tape induction components and introduces no claim of a completed BB(6) decision.
