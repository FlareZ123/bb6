# Full-rectangle synchronization language for machine #623

**Status:** exact finite-automaton construction, four-residue criterion, closed-form generic-word density, and finite authentic-root diagnostic. Intermediate: none proves the all-time authentic-root language.

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

## Exact arithmetic meaning of the two largest sink components

The nonaccepting graph of the 70-state DFA contains two especially prominent terminal SCCs. They are not opaque automaton artifacts.

For the 3-state SCC `{54,55,56}`, assign carries `0,-1,-2` respectively. Every internal edge labelled by digit pair `(x,y)` satisfies

[
x-3y+c = 3c'.
]

With the shifted carries `-1,-2,-3`, the same edges satisfy

[
x-3y+c = 3c'+2.
]

Thus this SCC is exactly the high-digit carry automaton for a ternary block of all 0s, or all 2s, in

[
X-3Y = 2(g-9q)-\gamma_s.
]

For the 6-state SCC `{18,19,20,37,41,57}`, assign zero-digit carries

[
18\mapsto5,;19\mapsto1,;20\mapsto2,;37\mapsto4,;41\mapsto6,;57\mapsto3.
]

Every internal edge satisfies

[
4x+3y+c=3c'.
]

Subtracting one from each carry gives the all-2 sign-extension version

[
4x+3y+c=3c'+2.
]

Hence this SCC is exactly the high-digit carry automaton for

[
4X+3Y = 2(4g+9q)-4\gamma_s.
]

These are precisely the two linear residuals appearing in the left/right terminal-predecessor strips. This explains why the hardest nonsynchronizing languages coincide with the terminal-cancellation obstruction: synchronization alone cannot magically remove the terminal-strip problem, because its recurrent failures literally encode those strips.

`DangerousResidualSCC.lean` proves the two coordinate identities symbolically with `omega` and checks every internal carry edge, including both 0- and 2-sign-extension labellings, by kernel computation. It compiles locally with Lean 4.36.0-rc2.


## Exact synchronization-language density

[ExactSynchronizationDensity.md](ExactSynchronizationDensity.md) proves analytically that, for every ternary digit-pair word length \(n\ge4\), **exactly \(3^{2n}-30\cdot3^n+291\)** of the \(3^{2n}\) words synchronize both full L/R rectangles. The proof is an explicit four-event inclusion–exclusion argument over the residue criterion; [count_sync_words.js](count_sync_words.js) independently enumerates the small cases. This is a count of *all words*, not authentic root windows. The generic infinite non-synchronizing words are exactly the union of 20 affine 3-adic lines, and the exact expected first-synchronization length for Haar-uniform words is 8239/1944 (about 4.238). Neither generic almost-sure synchronization nor the observed near-uniform prefix histogram implies an authentic-root invariant. It pinpoints why authentic source compatibility is essential.

## Extended authentic-root finite check (not a proof)

[root_sync_fast_scan.js](root_sync_fast_scan.js) is a **resumable** exact BigInt root scanner using upstream original highLevelNext for the small prefix, then the source-certified 3-state ternary drain transducer and canonical output formulas. Its first 2,000 transitions were independently compared against a literal original-evaluator implementation with zero disagreements. The [50,000-transition checkpoint](root_sync_extended_checkpoint.json) has **49,968 tested S-windows from section indices 33 through 50,000, with no full-rectangle synchronization failures or halting**, and preserves exact current counters so another researcher can resume without replaying the prefix. This is *only finite computation*: generic-word bad probability decreases rapidly with growing S-window length, and neither this scan nor the abundant synthetic cone counterexamples resolve the blank-root all-time invariant. Do not treat the 50k prefix as evidence that root reachability follows from cone membership alone.

## Sharp two-digit reset completion

[SharpTwoDigitCompletion.md](SharpTwoDigitCompletion.md) proves a stronger **all-prefix** fact about the full-rectangle synchronization language: for **every** length-\(n\ge3\) word, at least **24 of the 81** two-pair-digit extensions synchronize both full rectangles, with **exactly 24** for the all-zero prefix. One additional pair is not enough in the worst case. The proof is a finite-field incidence count of four explicit forbidden modular strips, independent of any finite scan; [count_two_digit_completions.js](count_two_digit_completions.js) enumerates all prefixes for n=3,4,5 as a reproducible check. This is an **existential word-completion** property, not a digit choice that the deterministic blank-root machine may make. The newly found source-authentic synchronization non-closure remains the principal obstruction to a root-only invariant.

## Joint synchronization + old-ray square-gap non-closure

[JointSyncSquareGapNonclosure.md](JointSyncSquareGapNonclosure.md) proves an **all-depth (\(\ell\ge30\)) original-source LE→LE cone-to-cone counterfamily** to the stronger **conjunction** of two proposed root invariants: full-rectangle S-window synchronization **and** \(h^2>5q\) old-ray square-gap. The source has huge \(g>8q\), satisfies the square-gap, and window word \((12,1)\) or \((13,1)\) synchronizing **both** rectangles. Its *actual* source successor has the **same S-window cut**, exact \(g'=5P\), window word \((9,2)\) or \((9,3)\) failing **left** synchronization, and \((h')^2<q'\), violating even the factor-one square-gap. The all-depth proof chooses q with controlled digit window and chooses c from **actual source drain statistics**, not from invented dynamics. [Independent BigInt source interpreter](verify_joint_sync_square_gap_nonclosure.js) checks 71 depths. Therefore **even synchronization and square-gap combined are not universally inductive**, despite source-certified cone membership; a blank-reachability/history invariant is indispensable. This does **not** show any failure on the actual blank-root orbit.

## Robust non-closure even at linear terminal separation

[RobustConeSyncNonclosure.md](RobustConeSyncNonclosure.md) strengthens the original cone-to-cone counterfamily: at **every mass depth \(\ell\ge30\)** there is an actual successful **LE→LE original-source transition** with identical source/target S-window cuts, both endpoints inside the original canonical cone, and even the strong pointwise inequalities \(g>4q/81\) at input and \(g'\le-2q'\) at target. Both conventional old-ray distances also satisfy the empirical factor-5 **square-gap** inequality \(h^2>5q\). Nevertheless the input full-rectangle window word \((N,1)\) synchronizes, while the target fails its full right rectangle. Its limiting gap ratios are \(10/79\) and \(701/237\); [BigInt original-source verifier](verify_robust_cone_sync_nonclosure.js) checks 71 parameter depths. This **rules out rescuing the universal synchronization induction using cone membership plus the proposed square-gap or even linear gap inequalities alone**. It does not contradict blank-root-specific synchronization.

## Infinite source-cone synchronization non-closure

[InfiniteConeSyncNonclosure.md](InfiniteConeSyncNonclosure.md) proves a **source-faithful unbounded counterfamily**: at every S-mass depth \(\ell\ge20\), a synthetic canonical LE-cone state has fully synchronizing S-window word \((0,1)\), while its **actual original-source** successor remains in the LE cone but fails the target full right-rectangle test. The tiny original-source example \(D(4388,1094)\to D(3284,3310)\) uses just **two** evaluator calls; its source word is \((0,1)\), target \((2184,3)\), and the target x+y residue is \(0\bmod729\). An [independent BigInt original-source reproducer](verify_cone_sync_failure_family.js) checks the small example and parameter depths 20–50. Consequently the proposed **universal** invariant (both cones + current synchronization ⇒ successor synchronization) is **false**, even on unbounded source-connected synthetic states. The actual blank-root-only invariant remains open; root-specific history is essential.

## Phase-correct global root-coordinate bridge

[GlobalSignedPQBridge.md](GlobalSignedPQBridge.md) restores the **exact** integer relation between canonical counters \((p,q)\) and the signed cocycle coordinates \(U=6q,\ V=2p-\gamma_s\), with sector phase \(\gamma_s=(18,10,2,4)\). Every one of the eight implied correction rows matches the existing \`SignedCoordinateNormalForm.lean\` table, including the RE full-drain convention. The previous blanket withdrawal should apply to **truncated moving-window propagation**, not to this global integer conjugacy: low-window quotient carry \(c_V\), source boundary phase and shifting window index still prevent a carry-free induction. The note includes the algebra and a coefficient-check reproducer.

## Unimodular two-coordinate reduction

[TwoCoordinate3AdicCocycle.md](TwoCoordinate3AdicCocycle.md) rewrites the exact four synchronization residues using the unimodular coordinates U = Y and V = X + Y.

The four forms are:
- V - 4U
- 3U
- 4V - U
- 3V

The two scale tests reduce exactly to residues of U and V modulo 3^(n-1). The exact branch updates become:
- Left: U' = 3U + φ; V' = V - U + κ + φ.
- Right: U' = 3V + φ; V' = U - V + κ + φ.

This is an exact algebraic reparameterization, not yet an all-time avoidance proof.
