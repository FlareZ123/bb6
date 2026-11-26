# Raw11 extra 28, D1=0LC: checked weighted bound 42

Status: local Lean 4.36.0-rc2 check against the compiled source artifact from Agent47's existing Raw11 route (artifact 15144626755). Not yet included in a global route certificate.

Exact parent: 1RB0LB_1RC1LC_0LA0LD_------_------_------ (extra index 28, zero-based in raw11-route.json).
Exact covered child: 1RB0LB_1RC1LC_0LA0LD_---0LC_------_------.
Theorem: BB6.Agent44Extra28D1LC.cover : Cover (WeightedBound bound) parent, bound = 42.
Axioms: propext, Classical.choice, Quot.sound only.

First-hole tree: 3309 nodes (2684 translated cycles, 349 last-hole leaves, 138 splits, 136 total closed-state leaves, 2 initially open).
One open leaf 1RB0LB_1RC1LC_0LA0LD_0RE0LC_1LD1RF_1RE--- is closed by two-stack automata with six states per stack.
The other, 1RB0LB_1RC1LC_0LA0LD_0RE0LC_1RF---_1LC1RE, has a direct binary-counter invariant. At E, the left half is a zero followed by k copies of 11 and arbitrary finite zeros. The right half consists of binary digits with zero separators. A 1 advances the carry in two transitions; a 0 sets the bit and resets k, using 3+2k+1 transitions. The blank run reaches the invariant in 12 steps. The symbolic proof never queries E1. Lean proves arbitrary-length runs and transfers them to the original compatible machine using the existing zipper/run soundness lemmas. Both never and cover are checked.

## Reproduction

Unpack source.tar.gz in an empty directory. With Python 3 and g++ installed, run:
    python generate.py
    python split.py

Extract the dependency artifact 15144626755, set LEAN_PATH to the working directory plus its a47-raw11-root52 directory, and use Lean 4.36.0-rc2 to compile, in order:
    Raw11Counter28
    Raw11Extra28D1LCBase
    Raw11Extra28D1LCPart0 through Part4 (independent)
    Raw11Extra28D1LCJoin

Use lean -o MODULE.olean MODULE.lean for each. The split is needed to avoid monolithic compilation timeout. The finite scanner uses bounded 128-bit tape encodings and treats overflow as unknown; none of its assertions are trusted by the kernel. The emitted proof checks every leaf and every normalized split, using the existing PhaseTree and PhaseFrontier libraries. No native_decide or sorryAx occurs in the printed axioms. SHA256 manifest identifies the locally checked sources. No new CI workflow.

## Remaining work

This closes one of the 20 normalized D1 children of extra 28. The 19 sibling cylinders remain to be handled or explicitly carried into the route frontier. The first-hole index and all split obligations must be checked before replacing extra 28 globally. This is not an unconditional proof for extra 28, Raw11, or BB(6).
