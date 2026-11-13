# m=2,n=4 even Q4 reset branch (intermediate)

**Status: Lean proof candidate, not yet kernel-verified.** Do not cite this as a proved TM63 stage or as a new Busy Beaver lower bound until the source module compiles under Lean 4.36.0-rc2 and its transitive axiom audit passes.

## Source and replay

- Lean development: [M2EvenQ4Prefix.lean](M2EvenQ4Prefix.lean)
- Deterministic bounded replay: [m2_even_q4_replay.py](m2_even_q4_replay.py)
- The Lean module reuses Agent 24's generic full-tape q4 suffix endpoint in `Q4RightEndpoint.lean` and Agent 48's counted-drain composition in `S1CountedDrain.lean`.

## New finite bridge

After the `3*a+2`-block counted left sweep from `s1Config 3 4 2 a 0 b h`, the local bridge input is

```lean
⟨3, 0, [-10,-9,-8,-7,-6,-5,-4,-1,2]⟩
```

The exact 50-step output is

```lean
⟨4, 2, [1,-1,-4,-7,-10,-11,-12,2]⟩
```

The visited heads are contained in `[-12,2]`. The bridge is followed by a `3*a`-step E-on-one scan to the Q4 cut at the original head `h`.

The parameterized prefix length is therefore

```
3*(3*a+2) + 50 + 3*a = 56 + 12*a.
```

At the cut, the left stream is the Q4 word
`[true] ++ d1pow a ++ markerWord 1 ++ d0 ++ binDec 3 3 ++ lh`,
and the right stream is the standard `q4RightFacing b` word. The generic suffix contributes `39+3*b` steps and reaches

```lean
s1Config 3 3 1 (a+b+2) (2^b-1) 0 (h+5+3*b)
```

The prefix-plus-suffix cost is

```
resetPrefixCost 2 4 a b = 95 + 12*a + 3*b.
```

The existing counted all-ones drain then transfers `2^b-1` into the right counter. The proposed complete increment endpoint is

```lean
s1Config 3 3 1 (a+b+2) 0 (2^b-1) (h+5+3*b)
```

with total cost `proposedIncrementCost 2 4 a b`, under `0<a`.

## Evidence boundary and next action

The finite bridge and the full reset-plus-drain behavior agree with a direct deterministic TM63 simulator for `0 ≤ a,b ≤ 4`. These are bounded computational checks only. The Lean module is not yet compiled; in particular, review the source-list boundary/tail identities, the Q4 cut tape extensionality, and the final counted-drain composition. Agent 24 has been asked for an adversarial source review and, if possible, a run through the existing **manual-only** source workflow. No push trigger or new per-lemma workflow was added.

This is an intermediate proof candidate under `im-results/`, not a publishable theorem in `results/`.
