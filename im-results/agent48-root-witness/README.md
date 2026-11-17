# TM63 blank-root to initial S1: kernel-checked prefix

Locally kernel-checked with Lean 4.36.0-rc2.

## Established theorem

The exact tm2 transition table from [ChampionRootBridge](../agent48-champion-root/ChampionRootBridge.lean), started on the blank tape, reaches the original source S1 configuration after exactly 27,959 successful moves:

\[
\operatorname{run}(\mathrm{tm2},27959,\mathrm{blank})
=\operatorname{some}(\mathrm{s1Config}\ 3\ 7\ 2\ 6\ 0\ 63\ 29).
\]

The theorem is BB6Coverage.Agent42InitialS1Root.tm2_blank_reaches_initialS1_source in [RootSourceBridge.lean](RootSourceBridge.lean). Its source configuration is the unchanged definition from [S1Encoder.lean](../agent8-s1-encoder/S1Encoder.lean), not a hand-written replacement.

The reached configuration has state 3, head 29, and 225 marked cells. Its exact finite support is

\[
\begin{aligned}
&\{31,32,33\}\ \cup\ \{36,\ldots,227\}\\
&\quad\cup\ \{12,\ldots,29\}\\
&\quad\cup\ \{11,10,8,5,2,-1,-4,-5,-6,-8,-9,-10\}.
\end{aligned}
\]

This matches the source S1 decomposition: d1pow 6, marker m2, the separate d0 delimiter, binDec 3 7 = d0^3, lh, and the right counter/RC suffix.

## Proof architecture

RootFiniteBits.lean uses a 238-bit Nat tape window for absolute cells -10 through 227, with head offset 10. bStep rejects any transition that would leave this window. The proof is not an unchecked finite simulator:

1. testBit_writeTape proves the bitset write operation has exactly the pointwise semantics of writing one cell.
2. embedB_move proves a successful bounded move embeds to the original infinite-tape applyMove.
3. bStep_sound and the inductive bRun_sound lift that correspondence to arbitrary successful finite runs.
4. tm2_blank_reaches_initialS1_bits checks all 27,959 transitions by kernel reduction using by decide. It does not use native_decide, an axiom for the computation, or a sorry.
5. RootSourceBridge.lean proves the final bitset agrees with the source S1 tape on every cell in the finite window, proves both tapes are zero outside it using the source left/right cell lemmas and exact side lengths, and composes the simulation theorem with the source equality.

The two modules print their axiom dependencies. The finite computation theorem reports [propext]; the original-source reachability theorem reports [propext, Quot.sound]. Neither reports sorryAx.

## New middle-source continuation (pending preflight)

The source-only middle continuation is being extended from the authentic initial S1 configuration through the established middle-26 endpoint and rows 27–34.

The former row-32 assumption has been replaced by the standalone theorem tm63_middle32_source in [TM63RootMiddle34.lean](../agent44-tm63-middle/TM63RootMiddle34.lean). It invokes the new valuation-parametric M1 source theorem in [M1EvenValuationSource.lean](../agent48-counted-inc0/M1EvenValuationSource.lean), which composes:

- the exact six-step S1 prelude and counted state-1/state-5 valuation bridge;
- the original-head q4 cut stream and complete right-side q4 shape;
- the generic q4 suffix and exact target-left identity;
- the reset intermediate and existing counted drain.

The M1 source theorem is stated for every positive n<2^L, with arbitrary 2-adic valuation. The root theorem now exposes tm63_blank_reaches_after_middle34 without a row-32 hypothesis; the old conditional name is retained only as a backwards-compatible wrapper.

**Validation status:** Agent 24 has independently reviewed the mathematical composition and found no substantive mismatch. Agent 7 has been asked to locally compile the exact dependency chain, and the manual workflow has been updated to stage and compile the new modules and inspect transitive axioms. This continuation is not yet compile-certified. Keep it in im-results until local preflight and targeted CI pass.

## Scope and remaining work

This is an initial-root prefix plus a source-level middle continuation, not a halting proof. It does not establish the complete champion itinerary, the terminal section, the exact primitive step score, a universal six-state upper bound, or the value of BB(6).

The next high-value integration is the formal 24-cycle row schedule/induction and its connection to the authentic middle-26 endpoint, followed by the remaining terminal itinerary and exact score. The generic M1 valuation source is designed to cover all marker-1 rows in that cycle; the other marker classes still use their corresponding source theorems.

The original simulation checkpoint and JS reproducer remain in [InitialS1RootWitness.md](../agent42-champion-terminal/InitialS1RootWitness.md). This result stays in im-results until the complete champion itinerary and exact score are established; it is not a standalone BB(6) result or a reason to change results/README.md.
