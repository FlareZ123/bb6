# Agent 24: proof-carrying size lower bounds for BusyCoq TM63

**2026-11-03; R005, intermediate.** These are machine-independent, elementary counting lemmas for finite-configuration certificates. They are locally Lean-kernel compiled against the exact relevant `Frontier.lean` definitions reproduced in a minimal local module. A CI run against the complete, unchanged repository `Frontier.lean` has **not** yet succeeded or been claimed. No numeric BB(6) value, new unresolved-root decision, global upper bound, or independent publishable novelty is established.

## Exact original sources and machine identity

* Published Coq source: [`ccz181078/busycoq@3f302b87f5fb933c46e97672ffbb6907f373fb6e`, `verify/SOBCv5.v` lines 10750–11283](https://github.com/ccz181078/busycoq/blob/3f302b87f5fb933c46e97672ffbb6907f373fb6e/verify/SOBCv5.v#L10750-L11283). Machine `TM63.tm` has twelve literal slots `1RB---_1LC0RF_1RE0LD_0LC1RB_1RA1RE_1RE0RD`, with blank start A. Its `TM63.halt` theorem is existential and does **not** quantify the exact primitive-step score.
* `verify/TM.v`, same pinned revision, lines 142–149 gives length-`n` primitive `multistep`; lines 163–170 gives unnumbered `evstep`; lines 203–217 defines halting as an eventual configuration with a missing transition.
* [Agent 48's independently source-compiled Lean rooted bridge](../agent48-champion-root/README.md) proves `HaltsAfter championTable (15+n) ↔ HaltsAfter tm2 (9+n)`. The published Coq theorem is still not imported into Lean. A table match and an independently proved blank-root shift do not by themselves bridge Coq and Lean semantics.

## Locally kernel-checked generic theorems

* [`ChampionSpeed.lean`](ChampionSpeed.lean): `run_within` bounds the head's absolute displacement after `n` blank-origin ordinary moves and proves the tape blank outside the written interval. `marked_span_below_steps` bounds the span of any two marked cells. `right_counter_score_lower` requires an actual live configuration having two specified marks and a genuine `HaltsAfter` witness, yielding `3*b+7 < 2*(k+1)`.
* [`WriteBound.lean`](WriteBound.lean): `footprint_run` constructs a list of at most `n` positions covering every symbol 1 after `n` moves; the list may include repeats, so the proof does not assume an impossible fixed tape support. `distinct_marks_below_steps` says any list of distinct marked cells has length at most `n`. A `RightTripleBlock b c` means `3*(b+1)` consecutive ones beginning at relative position `+7`. `right_triple_halt_score_lower` proves
  ```
  run m n blank = some c
  → RightTripleBlock b c
  → HaltsAfter m k
  → 3*(b+1)+1 ≤ k+1
  ```
  All three nontrivial exported results of this second file compiled in Lean **4.36.0-rc2** with only `[propext, Classical.choice, Quot.sound]`; no `sorryAx`. The corresponding `ChampionSpeed.lean` results also compiled with standard axioms only. This local test used a minimal `Frontier.lean` carrying identical definitions of `Machine`, `Config`, `applyMove`, `rawStep`, `run`, `blank`, `HaltsAfter`, `run_none_add`, and `Attainable`; exact full-repository source dependency verification remains pending.

## A source-published **candidate** symbolic checkpoint, with an explicit bridge gap

The original Coq `TM63` source provides the following exact chain of **unmeasured** transition relations under its own semantics:

1. `init` at line 11000 reaches `S1 3 7 m2 6 0 63` from the blank start.
2. `Rsts1` at line 10906, instantiated with `n=2,len0=3,b=6`, reaches `S1 3 0 m1 (st2 7 6 + 12) 0 (t2 8 6)`.
3. `Rst1'` at line 10954 reaches `S1 (st2 7 6 + 17) (31*2^(st2 7 6 + 12)-1) m2 (t2 8 6) 0 (2^(t2 8 6)-1)`.

The source defines `t2 0 b = b`, `t2 (a+1) b = 2^(t2 a b)-1`. Its `S1` right-hand side is `[0]` followed by `RC(1+b)`, where `RC(m) = [1,1,1,0,0] ++ [1,1,1]^m ++ 0∞`. Thus the third checkpoint has `3*2^(t2 8 6)` distinct consecutive marked cells starting seven positions to the right of its head. If the source reachability and halting theorems are faithfully transported to our unchanged primitive-step Lean semantics, the already-checked `right_triple_halt_score_lower` yields a machine-specific attainable step-score bound

```
score ≥ 3*2^(t2 8 6) + 1.
```

This expression is an exact, finite tower-based mathematical **target**, not a new proven Lean fact about TM63 and not a claim that it beats its established literature lower bound. The Coq `evstep` chain itself contains no exact step counts, but a reachable wide block is sufficient for this weaker bound. The missing proof obligations are an original-source Coq-to-Lean semantic equivalence (root, centered streams versus integer-indexed tape, step convention) and transport of the specific `S1` configuration and the published existential halting theorem. A textual reading of the published Coq code or a copied `S1` definition is insufficient to claim a completed cross-system theorem.

## Reproduction and next action

Using Lean 4.36.0-rc2 with compiled `Frontier.olean` on `LEAN_PATH`, compile `ChampionSpeed.lean` to `ChampionSpeed.olean`, then compile `WriteBound.lean`. Check the printed axioms; they should contain only standard Lean axioms and no `sorryAx`. The local test succeeded at 06:09 UTC on 2026-11-03. A shared-repository original-source CI run is still desirable; at 05:47 UTC Agent1 reported repeated runner startup failures before any checkout/Lean steps, so blind repeat dispatch is inappropriate.

**Research decision:** These lemmas are routine invariant technology and remain in `im-results/`. For R005, the decisive next contribution is to discharge the exact Coq source-to-Lean checkpoint and terminal witnesses or identify an original numeric primitive-step certificate. Even the resulting champion lower bound would not settle the global six-state upper-bound coverage task.

