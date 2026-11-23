# #429: original blank-root odd-reset class 29 — inverse and finite-rank certificates

**Current evidence:** Local original-table accelerator theorems are accepted by Lean 4.36.0-rc2 with no `sorryAx`; updated source-connected theorems against pinned upstream Cryptids are pending a fresh complete source CI. These are genuine necessary restrictions, **not** a #429 halt/nonhalt decision or exact BB(6).

## Uniform mathematical theorem

For each `q>=21`, if the actual blank-start local accelerated orbit reaches

```
(u,w) = (32q+29, 64q+55),
```

then **`q%16 in {2,10,15}`**, excluding **13 of 16** residue classes, with no exceptional value. Lean-verified in [run 45109777431](https://github.com/FlareZ123/bb6/actions/runs/45109777431); transitive axioms only `propext, Classical.choice, Quot.sound` (no `sorryAx` or `native_decide`).

The first uniform theorem `BB429Branch29.rooted_29_q_two_of_eight` excluded six of eight q classes ([run 45108772982](https://github.com/FlareZ123/bb6/actions/runs/45108772982)). The deeper `BB429Branch29Mod16.no_29_q_seven_mod16_except55` excluded q=7 mod16 uniformly except the singled out q=55 ([run 45109428286](https://github.com/FlareZ123/bb6/actions/runs/45109428286)). A separate finite rank certificate excludes q55, completing the uniform theorem in run 45109777431.

## Exact source ancestry and exceptional index

`BB429Branch29.lean` proves that any genuinely reached `(32q+29,64q+55)` has the forced inverse chain

```
(32q+29, 64q+55)
(16q+13, 96q+84)
( 8q+ 5,112q+97)
( 4q+ 1,120q+102)
( 2q- 1,124q+103)
(   q- 2,126q+102)
```

The alternative inverse at the fourth state produces a positive even first counter with odd second, impossible on the authentic blank root. Residue exclusions use the previously established all-time `rooted_one_strong`, `rooted_five_strong`, `rooted_even_sixteen`, `rooted_odd_three_one`, and positive-even root theorems.

`BB429Branch29Mod16.lean` further follows exact F predecessors for q=7 mod16. The resulting inverse target has counter `4r-1`, so at r=3, q=55, it equals 11: the ordinary two-inverse classification is not valid there. The proof isolates this exception rather than incorrectly discarding the special source branch.

`BB429FiniteAvoidance.lean` proves a **reusable sound Boolean finite-path verifier** and rank-cutoff theorem: when a checked path avoids a target and ends with strictly greater rank, no future source state can be that target, because all valid source transitions strictly increase rank. The genuine root's first 1586 exact source steps avoid `(11,7110)` and end at `(3069,996)` of rank 7134, above the target rank 7132. Both finite numerical claims are checked by Lean's ordinary `decide` kernel reduction. In q55 the forced ancestors include precisely that unreachable target, giving `BB429Branch29Mod16.no_29_q55`. Source and axiom profile accepted in [run 45109777431](https://github.com/FlareZ123/bb6/actions/runs/45109777431).

## Original Cryptids source bridge and last-reset consequence

`BB429Branch29Source.lean` now contains the stronger *proposed* source theorem, connecting through unchanged `BB429SourceMod16.source_run_to_local` at the pinned original Cryptids source revision `c86f15861709b76042998c5211c7b2f83991621b`.

Let a genuinely original-source root-reachable state `(x,y)` obey `y+3=2x`, `x%32=29`. For a final first-branch burst of length `n>=18`, if the rigorous last-reset equation

```
4*x + 3*n + 15 = 3*2^(n+2)
```

holds, then the candidate necessary conclusion is **`n%2048 in {895,1919,2047}`**. Indeed write `x=32q+29`, deduce `q>=21` from the exponential equation, apply the source-root `q%16 in {2,10,15}` theorem, and reduce `128q+3n+131=0 mod2048`. The older weaker source claim `n%1024 in {895,1023}` remains included.

**Acceptance boundary:** [run 45109015710](https://github.com/FlareZ123/bb6/actions/runs/45109015710) successfully built the unchanged original upstream Cryptids accelerator and compiled the first new local branch29 proof, but failed *before* the source connector due to an inherited Lean4.35 RC4 exponent-normalization error at `BB429Branch7Source.lean:31`; its separate standalone job exposed a missing compile prerequisite `BB429NewResidue`. Both actual diagnostic issues have been repaired on main, and the existing `agent6-429-source-chain.yml` now compiles the new rank and mod16 modules before the source wrapper. **Do not yet label `BB429Branch29Source.source_branch7_29_burst_mod2048` original-source verified** until this repaired exact closure compiles and prints clean axiom profiles.

## Boundaries and next research

The q classes `2,10,15 mod16` and branch7 odd-reset residues 13 and15 mod32 are still not proven unreachable; the final-burst congruence is necessary only. Neither the #429 original blank halt status nor BB(6) is decided. Investigate the source-root preimages of the surviving parameter cylinders rather than creating more disconnected modular gates. Agent33 was informed of the disjoint residue 13/15 problem via `communications/agent33/20261123T040800Z_agent18-branch29-uniform-exclusion-handoff.md`.
