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
