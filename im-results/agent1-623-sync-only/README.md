# Full-rectangle synchronization language for machine #623

**Status:** exact finite-automaton construction plus finite authentic-root diagnostic. Intermediate: it does not prove the all-time root language.

## Key separation

The existing common-reset language bundles two logically distinct properties:

1. every allowed L and R boundary carry state is synchronized to one branch-specific state;
2. the produced x digits are nonmonochromatic (contain a digit different from 0 and a digit different from 2).

The current D653 S-window separates them: it fails property 2 for five synthetic R starts, but it **does** synchronize all 225 L starts and all 270 R starts after three symbols.

This dossier therefore isolates **synchronization only**.

## Exact automaton

Starting from the full rectangles

- L: 9 previous digit pairs times x-carry [-2,2] times y-carry [-2,2] = 225 states;
- R: 9 previous digit pairs times x-carry [-4,1] times y-carry [-2,2] = 270 states,

take the deterministic image pair after each input symbol. There are exactly **355 reachable image-pair states**. Minimizing the language "both images are singleton" yields an exact **70-state DFA with one accepting state**.

The full table is `FullRectangleSyncDFA.json`; `build_full_rectangle_sync_dfa.js` reconstructs it from the carry equations and checks the 355/70 counts.

This automaton is materially smaller and conceptually cleaner than the reset-pattern recognizer because it does not carry output flags.

## Authentic-prefix diagnostic

Running the exact correction-only target words `[k_S+2,j_S-2)` for source transitions 33..10000 through the 70-state synchronization DFA gives:

- 9,968 / 9,968 accepted;
- first synchronization after 3..12 symbols;
- histogram: 3:2642, 4:4042, 5:2093, 6:782, 7:268, 8:96, 9:27, 10:9, 11:7, 12:2;
- the two length-12 cases are source transitions 3383 and 6931.

This includes D653, whose word is not accepted by the current common-reset DFA.

## D653 obstruction is output-only

For the D653 word
[
[3,7,5,3,1,5,6,6,7,5,5,5],
]
both full carry rectangles synchronize after its prefix `[3,7,5]`.

For L, all 225 starts also satisfy the nonmonochromatic output condition. For R, exactly five starts fail it, and they are precisely

[
(mathrm{prevX},mathrm{prevY})=(2,2),qquad
mathrm{carryX}=-4,qquad
mathrm{carryY}in{-2,-1,0,1,2}.
]

The authentic R state entering the D653 word is `previous_pair=(1,0), carry=(-3,1)`, so its produced x digits are nonmonochromatic. Thus the finite D653 failure is caused by the old recognizer quantifying over unreachable-for-this-edge synthetic starts, not by the authentic transition.

## Research consequence

A cleaner all-time proof target is now available:

- prove the authentic S-window language enters the accepting state of the 70-state **synchronization-only** DFA;
- handle output nonmonochromaticity separately, using the exact synchronized state/suffix and only the actually reachable boundary phases.

This avoids demanding a single universal pattern simultaneously solve carry synchronization and output separation. The finite scan is evidence for this decomposition, not an induction proof.
