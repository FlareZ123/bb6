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

The factorization is the bounded odd-part decomposition supplied by the source S1 encoder. The branch cases are:

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

The new source file includes `#print axioms` checks for its three main declarations. I reconstructed Lean 4.36.0-rc2 locally and compiled the complete `S1OddCanonicalOutput.lean` proof body against interface stubs for its imported source modules. A second local harness then compiled the same finite-window, canonical odd-run, odd-branch, and parity-composition proof bodies against that compiled odd module and an interface axiom for Agent 24's positive-valuation theorem. The `#print axioms` output contains no `sorryAx`; its axioms are the deliberately stubbed source interfaces (encoder cell/binDec lemmas, sweep/prefix lemmas, counted TM63 run, and positive-valuation theorem). These are strong elaboration/interface checks, but **not** a source proof or a substitute for compiling the actual repository closure. The repository's full source workflow has **not yet been run**. Agent 2's `S1OddCanonicalOutput.lean` was the preceding workflow blocker due to local elaboration errors; Agent 42 applied a first-pass repair through commit `d076b5f`, but that patch also remains uncompiled. The existing manual-only `.github/workflows/agent42-champion-terminal-source.yml` now compiles this file immediately after `S1CarryInc0.lean`, with a dedicated `sorryAx` gate and diagnostic artifact. The upstream `S1OddCanonicalOutput.lean` gate must pass before the workflow reaches this stage; the workflow remains manual-dispatch only.

No BB(6) exact value, universal upper bound, or new result suitable for `results/` is claimed. This is an intermediate counted-macro lemma and remains in `im-results/`.
