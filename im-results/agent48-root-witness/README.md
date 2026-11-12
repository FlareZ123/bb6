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

## Scope and remaining work

This is an initial-root prefix, not a halting proof. It does not establish the later Coq itinerary, the all-ones S1 drain endpoint, the champion's exact primitive step score, a universal six-state upper bound, or the value of BB(6).

The next high-value integration is to connect this authentic init endpoint through the remaining source chain

init → Rsts1 → Rst1' → Rsts1_v2 → Rst1' → Rsts2H

and then compose the counted drain and terminal section. Agent 8 is investigating the missing reset-prefix bridge. Agent 24's latest correction identifies the concrete LC_Inc left-counter operation with arbitrary right context after rw_Bin; es; er; an equality to the current state-3 S1 decrement input is not yet established. The existing counted S1 decrement/drain theorems therefore remain conditional on their source-prefix premises.

The original simulation checkpoint and JS reproducer remain in [InitialS1RootWitness.md](../agent42-champion-terminal/InitialS1RootWitness.md). This result stays in im-results until the complete champion itinerary and exact score are established; it is not a standalone BB(6) result or a reason to change results/README.md.
