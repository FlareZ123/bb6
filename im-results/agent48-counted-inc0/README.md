# Parity-complete source S1 counted decrement

**Status: intermediate proof candidate; not yet compiled against the repository source closure.**

This module composes the two existing TM63 counted branches into one canonical S1 decrement statement.

## Main theorem

`S1CountedInc0.lean` proves the candidate theorem

```lean
s1Config_counted_decrement
  (L n m a z b : Nat) (h : Int)
  (hz : 0 < z) (hzlt : z < 2^a) :
  ∃ q r len, z = (2*q+1)*2^r ∧ a = len+1+r ∧ q < 2^len ∧
    run tm2 (48+12*r+12*b) (s1Config L n m a z b h) =
      some (s1Config L n m a (z-1) (b+1) h)
```

The factorization is the bounded odd-part decomposition supplied by the source S1 encoder. The file also exposes `s1Config_counted_decrement_odd` for the valuation-zero branch independently. The branch cases are:

- **r = 0 (odd z):** use the original `counted_odd_counter` 48+12b source run. The new `s1Config_oddCounter_countedReturn_canonical` theorem connects its exact output tape to the canonical S1 encoding of (z-1,b+1), using Agent 2's `oddCounterOutput_s1Successor`.
- **r > 0 (even z):** reuse Agent 24's `s1Config_counted_decrement_allPositive`, which already composes the arbitrary positive-valuation carry prefix and open-head suffix into the canonical S1 successor.

Thus the branch-specific "S1 successor" is indeed a decrement of the encoded binary counter by one, together with an increment of the unary counter. The runtime formula is 48+12*v₂(z)+12b, with r=v₂(z).

## Dependencies and ownership

The new file imports:
- `im-results/agent24-champion-time/S1CarryInc0.lean` (positive-valuation branch);
- `im-results/agent2-inc0-odd-canonical/S1OddCanonicalOutput.lean` (valuation-zero output identity);
- through those modules, the existing original-table TM63 counted sweeps, carry-prefix, S1 encoder, and terminal-frame lemmas.

It does not modify Agent 24's even branch, Agent 42's prefix bridge, or Agent 2's odd-output source module. The only new source-side work here is the valuation-zero S1 input/frame lift and the parity-composition theorem.

## Verification status

The parity module includes `#print axioms` checks for its principal declarations. I reconstructed Lean 4.36.0-rc2 locally and compiled the complete `S1OddCanonicalOutput.lean` proof body against interface stubs for its imported source modules. A second local harness compiled the finite S1 input-window proof, canonical odd run, odd-only decrement, and parity-composition proof bodies against that compiled odd module and an interface axiom for Agent 24's positive-valuation theorem. During this work, the odd module was repaired at the source level: cast lemma names, the let-bound negative-left index split, absolute coordinate association, frame simplification order, and the outer right-sweep cutoff were corrected. The `#print axioms` output from the local harness contains no `sorryAx`; remaining axioms are the deliberately stubbed source interfaces (encoder cell/binDec lemmas, sweep/prefix lemmas, counted TM63 run, and positive-valuation theorem). These are elaboration/interface checks, **not** a source-closure proof. The actual repository workflow has **not yet been run**. The manual-only `.github/workflows/agent42-champion-terminal-source.yml` compiles `S1OddCanonicalOutput`, `S1CarryInc0`, `S1CountedInc0`, and `S1CountedDrain` in dependency order, with dedicated `sorryAx` gates and diagnostic artifacts; it remains `workflow_dispatch` only.

No BB(6) exact value, universal upper bound, or new result suitable for `results/` is claimed. This is an intermediate counted-macro lemma and remains in `im-results/`.


## Whole S1 all-ones drain

Added `S1CountedDrain.lean` to instantiate Agent 8's generic `CountedReset.countedIncs0` theorem. The encoder definition is the key interface identity:

```lean
s1Config L n m a z c h =
  s0Config (markerWord m ++ d0 ++ binDec L n ++ lh) a z c h
```

The parity-complete one-step theorem therefore supplies the uniform S0 Inc0 premise after rewriting its factorization witness with Agent 8's `v2_of_odd_factorization`. The new source theorem states that, whenever `2^k-1 < 2^a`,

```lean
run tm2 (drainCost (2^k-1) c)
  (s1Config L n m a (2^k-1) c h)
  =
  some (s1Config L n m a 0 (c+(2^k-1)) h)
```

For initial unary counter zero, Agent 8's existing valuation-pattern identity and closed form give the exact all-ones drain runtime:

[
6\cdot 4^k + 42\cdot 2^k - 12k - 48.
]

The module exposes `s1Config_counted_drain`, `s1Config_counted_drain_pattern`, and `s1Config_counted_drain_closed`. This is a composition of the source-level one-step S1 theorem with Agent 8's generic S0 drain theorem; it does not independently re-prove the repeated-run semantics or the v₂ carry-pattern identity.

The same local interface harness used for the parity theorem type-checks the new whole-drain composition with the source S1 decrement theorem and CountedReset interfaces represented by axioms. The actual repository source workflow has been extended to compile and `sorryAx`-audit `S1CountedDrain.lean` immediately after `S1CountedInc0.lean`. Neither new source module has yet passed the complete repository workflow.


## Champion terminal bridge: discharge its Inc0 premise

Added `S1ChampionCountedReset.lean`. The terminal bridge fixes its S0 left context to

```lean
markerWord 0 ++ d0 ++ binDec L 0 ++ lh
```

which is definitionally the S1 configuration `s1Config L 0 0`. Therefore `s1Config_counted_decrement` at parameters `(L, 0, 0)`, together with Agent 8's `v2_of_odd_factorization`, supplies the bridge's entire uniform Inc0 hypothesis for every `z>0`, `z<2^(a+b+resetDelta m)`, and every unary counter c.

The new theorem `champion_attainable_after_s1_countedRst012` specializes `champion_attainable_after_countedRst012` and removes its generic `hInc0` argument. Its remaining machine-specific hypotheses are:
- a genuine blank-root run `hblank` to the configuration cfg;
- a reset-prefix run `hprefix` from cfg to `s1Config L 0 0 (a+b+resetDelta m) (2^b-1) 0 h`;
- the existing positivity condition `0<a`.

This does **not** prove the blank-root or reset-prefix witnesses. It isolates the remaining champion obligation as the prefix reachability theorem, rather than leaving the generic one-step decrement premise as a separate dependency. The module locally type-checks against interface stubs for the source S1 theorem and terminal bridge. The manual workflow now compiles it immediately after `TerminalEncoderBridge.lean` and audits its axioms for `sorryAx`.


The intended Agent 42 pre-drain prefix target has left context
`markerWord (nextMarker m) ++ d0 ++ binDec L (n-1) ++ lh`. Since
`nextMarker m = (m+2)%3`, the terminal bridge's fixed context is reached at
`m=1,n=1` (`nextMarker 1=0`, `1-1=0`). The module therefore also exposes
`champion_attainable_after_s1_countedRst012_m1n1`, whose prefix premise is
written directly in the terminal bridge's S0 form. This is the exact parameter
specialization to target once the Rst0/Rst1/Rst2 prefix theorem is source-proved.

## Blank-root q4 drain composition (new source proof candidate)

`TM63RootQ4Drain.lean` now composes three existing original-table run
interfaces into one blank-root prefix:

1. `tm2_blank_reaches_initialS1_source`: 27,959 moves from blank to
   `s1Config 3 7 2 6 0 63 29`, using the bounded-bitset computation and
   the complete infinite-tape encoder bridge in
   `im-results/agent48-root-witness/RootSourceBridge.lean`.
2. `tm2_q4_root_source`: 332 moves to
   `s1Config 3 6 1 71 (2^63-1) 0 223`, the exact q4 target.
3. `s1Config_counted_drain_closed`: the all-ones 63-bit drain costs
   `6*4^63 + 42*2^63 - 804` moves and ends at
   `s1Config 3 6 1 71 0 (2^63-1) 223`.

The composed theorem is
`BB6Coverage.Agent48CountedInc0.tm2_blank_reaches_q4_drain_endpoint`.
Its total run length is exactly

`6*4^63 + 42*2^63 + 27487`.

The authored theorem is intended to certify an original-source run
prefix from the genuine blank tape, not a finite-window extrapolation. If
its full import graph compiles, the successful `run` witness establishes
that TM63 executes at least this many primitive moves. It does **not**
establish that the endpoint halts, that TM63 is a halting champion, or
that this is a Busy Beaver lower bound. The q4 source endpoint, the S1
counted decrement chain, and the all-ones drain still require a combined
original-import Lean 4.36.0-rc2 compile with a clean transitive axiom
audit. The new composition module has been added, but that combined
workflow has not yet been run; treat the theorem as a proof candidate.


## Odd inner-counter reset base: canonical endpoint (new proof candidate)

Added `ResetOddCanonical.lean`. It closes the frame-to-encoder equality left open by `CountedResetOddBase.resetBase_odd_frame` and Agent 24's `ResetOddCanonicalization.md`. The main theorem is

```lean
resetBase_odd_canonical
  (L n m : Nat) (h : Int) (hm : m < 3)
  (hn : n % 2 = 1) (hbound : n < 2^L) :
  run tm2 (resetPrefixCost m n 0 0)
    (s1Config L n m 0 0 0 h) =
    some (s1Config L (n-1) ((m+2)%3) (resetDelta m) 0 0 (h+5))
```

The proof splits the tape comparison into (i) exact finite output agreement inside the marker-specific reset frame, (ii) a common `binDec (L-1) (n/2) ++ lh` left tail outside the frame, with the single m=2 boundary cell handled by the shared third bit of d0/d1, and (iii) the blank right tail after the nine-cell right stream. It also derives the exact `binDec L (n-1) = d1 ++ binDec (L-1) (n/2)` rewrite and converts the framed result to the canonical shifted S1 configuration.

**Verification boundary:** this is a newly authored Lean proof candidate and has not been compiled. It depends on `CountedResetOddBase.lean`, `CountedResetBase.lean`, `CountedReset.lean`, and their source dependencies. It covers only odd inner n with a=b=0; it does not discharge the general reset-prefix obligation or the root's next n=6 even stage. Keep it in `im-results/` until a source-pinned Lean compile and `sorryAx` audit pass.


## Root's next reset stage: even n=6, marker m=1 (new q4 cut candidate)

Added `M1EvenQ4Prefix.lean`. This addresses the concrete next source state after the root q4/drain endpoint, `s1Config 3 6 1 a 0 b h`, rather than the already-covered odd `a=b=0` base. The main theorem `m1Even_q4_prefix_run` proves a source run of `44+12*a` moves to state 4 at head `h+4`, with an explicit tape `m1EvenQ4CutTape a b h`. The proof is decomposed into:
- `counted_left_sweep (3*a+1)`, costing `9*a+3`;
- a fixed 41-step framed bridge with input marks `[-7,-6,-5,-4,-1,2,3,4]` and output marks `[-9,-8,-7,-4,-1,1,2,3,4]`;
- `E_scan (3*a)`, returning the head to `h+4`.

The companion theorem `m1Even_q4_prefix_rightShape` establishes the exact `q4RightShape` precondition for the existing `Q4Suffix`. The module also proves `m1Even_q4_suffix_after_four`, reusing the existing suffix after the four already-consumed state-4-on-one transitions, and `m1Even_reset_prefix_frame`: a complete source run of `79+12*a+3*b` moves from the m=1,n=6 S1 input to the exact explicit Q4 suffix output frame. This total matches `resetPrefixCost 1 6 a b` (since `v2 6=1`).

**Verification boundary:** the new m=1,n=6 theorems are uncompiled candidates. The q4 cut's canonical left-facing identity is now stated as `m1Even_q4_prefix_leftFacing`, with explicit target word `m1EvenQ4LeftFacing a`. The remaining task is to identify the final Q4 suffix frame with `s1Config 3 5 0 (a+b+2) (2^b-1) 0 (h+5+3*b)` using the corresponding suffix left-tail identity. All new declarations remain uncompiled proof candidates. Keep this in `im-results/`; it is not yet a complete canonical reset-prefix theorem.
