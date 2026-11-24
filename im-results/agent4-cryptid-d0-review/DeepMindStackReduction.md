# External exact stack reduction for Cryptid D / BB(6) #490

**Classification:** intermediate research lead. This is an existing external formalization, not a new result of this repository and not a halt/nonhalt decision.

## Exact source and pin

At Google DeepMind's `google-deepmind/cryptids`, commit
`3647718b5df22e1a61462dec0376bd204526285a` (2026-11-12), the file

- [`BusyBeaver/BB6/Accelerations/M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH.lean`](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/Accelerations/M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH.lean)
- blob SHA256-independent Git blob id: `f0bc716f48f69ffff474c8094c3254eaf7681acb`

formalizes exactly the local target table
`1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`
(with F/1 represented as the explicit halt `HHH`).

The file identifies it as wiki holdout #490, the same transition table as #85 after a state permutation and left/right reflection. Its state map from #85 to #490 is
`f = ![5, 4, 2, 0, 1, 3]`; the transition-table identity `hM` is proved by exhaustive finite cases. The target blank start (state A) corresponds to #85 state D under this map and reflection.

## What is formally proved

The external module imports the #85 closed pair-stack system and transports it by `ClosedStackSystem.mirror`. Its main declarations are:

- `hM`: exact transition-table isomorphism under `f` and reflected directions.
- `closedStackSystem`: the mirrored closed stack system for #490.
- `init_reaches_nontrivial`: the blank-tape target reaches a nontrivial stack configuration in **7 raw steps**:
  `StackMode.DR_n_n`, left stack `[(0,0),(0,0)]`, right stack `[(1,0)]`.
- `has_stack_reduction`: a `HasStackReduction target` certificate.

The transported stack system has four modes `CR_n_n`, `EL_n_n`, `DL_0_n`, `DR_n_n`, and two stacks of natural-number pairs. The generic encodings in `BusyBeaver/BB6/Accelerations/Stack.lean` represent stack entries by unary runs separated by zeroes. The source proves the stack-language is closed under a positive machine run to another stack configuration or the halt transition; it also proves the inner token/bounce routines terminate using a well-founded bounded-lexicographic argument.

This is a stronger all-time *representation* of the root orbit than a finite prefix trace. It is not an eventual-halting theorem: `has_stack_reduction` only establishes a closed accelerated state space and an initial nontrivial stack entry.

## External hardness classification — heuristic only

The same pinned repository's `BusyBeaver/BB6/Hardness.lean` groups #85/#285/#490/#500 as one stack cryptid. It records the community's RES trigger: a particular 107–110-residue sequence modulo 3 must occur at an empty-left reset; the main number grows by approximately (8/3) per era; no shield is known. For #490 it cites @-d's 108-residue halting path and a search of about 235,000 right-side words, and records a heuristic expected halt around (10^{10^{38.1}}) steps. The same file labels the case open. These are community/heuristic statements, not theorems in the stack-reduction module.

## Why this matters to the local D programme

The local D work has source-certified canonical sections (I_a((01)^q1^b)), an eleven-row `DRegular.next` map, the 3-adic shift identity, and the exact TM62 halting-cylinder bridge. The DeepMind representation instead supplies a full closed pair-stack state space containing the actual blank root after seven steps. It is therefore a genuinely different coordinate system for the same machine, not another simulation of the DRegular orbit.

The stack coordinates may be the natural home for the required nonregular invariant or for a proof that the root eventually hits the RES trigger. They also provide a useful independent cross-check of the DRegular source map. However, the RES trigger is an exact finite-word reachability question along one deterministic stack orbit; a probability estimate or a finite search does not settle it.

## Concrete next work

1. Translate the 7-step stack entry and the first stack-mode transitions into the local `CryptidBoundary` representation, so the external stack orbit and local `I_a(w)` orbit have an explicit source-connected commuting diagram.
2. Extract the stack-system return map at empty-left resets and express its RES trigger as a precise residue-word predicate on the stack state.
3. Compare that predicate with the local halting-cylinder congruences (a\equiv C_w\pmod{3^{108+z(w)}}). A useful result would be an exact equivalence, not a finite correlation.
4. Then pursue either (a) a deterministic proof that the authentic stack orbit reaches a trigger word, with exact raw step accumulation, or (b) an inductive nonregular invariant excluding every trigger. Do not treat the heuristic “probviously halting” classification as a proof.

No files under `results/` should be changed on the basis of this external reduction alone.
