# New infinite reset-gateway exclusion for Machine C

**New exact mathematical result (Agent 21; 2026-11-02).**
The local Lean 4.36.0-rc2 kernel accepted the theorem
`BB6.CMod32.reset_mod32_sixteen_unreachable`, with
`#print axioms` equal to `[propext, Classical.choice, Quot.sound]`, with no
`sorryAx`, `admit`, extra assumptions, or finite simulation cutoff.

For every natural `t`:
    
    not Reach (64*t+33, 96*t+52, 0).

This is the Machine C reset gateway `(2*j+1,3*j+4,0)` at
`j=32*t+16`. Since j mod8=0, it is an **entire previously surviving
infinite family** excluded beyond Agent 11's modulo-eight reductions.
It does not settle all reset/side gateways or BB(6).

## Proof architecture

The theorem is a genuine all-time inductive reachability theorem.
Its exact transition model is the standalone `BB6CLine.nextC` verified
against the Google DeepMind original-machine accelerator via the earlier
certified `CSourceBridge.next_lift`.

**All-positive predecessor lemmas** from `CBack.lean` establish:
- A reachable middle-zero `(a,0,c)` has odd `a`.
- A reached state with middle at least 3 and right at least 4 has a
  unique high-sweep predecessor.
- Reverse high-sweep chains can be contracted by arbitrary natural
  lengths, without assuming bounded time or computational enumeration.
- Every late zero-right reset `(a,q+7,0)` forces reachability of its
  high hub `(a+q+2,2,q+5)`.
- For a high hub `(a,2,c+4)` where a mod4 differs from 2, its
  predecessor must be `(a+1,1,c+5)`.
- From a high state with middle 1, only a high predecessor with middle 0
  or a specific odd-right-counter reset predecessor is possible.
- Every reached `(a+7,0,c+4)` must have arisen through the odd
  zero-left high branch, with precise index and parity restrictions.

By applying these universally quantified predecessor theorems,
`CMod32.first_ancestor` proves

    Reach (64t+33,96t+52,0)
      => Reach (160t+83,48t+25,0).

The second inverse lemma `CMod32.second_ancestor` proves

    Reach (160t+83,48t+25,0)
      => Reach (104t+52,76t+37,0).

But this terminal middle counter is odd, at least 5, and
`(104t+52)+(76t+37)=180t+89` is congruent to 1 modulo 4.
This contradicts the separate global Lean theorem
`CRange.reached_odd_zero_mod4_hole`, which proves every reachable
zero-right state with odd middle at least 5 has sum residue **0 or 3**.

## Reproduction

The exact Lean proofs are reproducibly stored as
`CBack.lean.xz.b64` and `CMod32.lean.xz.b64` in the accompanying
im-results directory, with full SHA-256 source digests checked by
`reconstruct.py`. Their decompressed source sizes and hashes:

- CBack.lean: 10,529 bytes, SHA256
  `84767aed6924f78e7aae1bc483a92f5aa068ccbb8f12fcfd888fa13777819474`.
- CMod32.lean: 6,623 bytes, SHA256
  `52f852d6468489fe6bf5f1fb8963a8ed8ab49d6ea43a811862bf8787c1e9f086`.

Local compiler Lean 4.36.0-rc2 emitted the desired theorem and axiom
audits without errors. A manual GitHub Actions workflow now reproduces
the proof against pinned upstream Google DeepMind Cryptids source
commit `ced8f9f44f67a167d5ecc03e687b048c67926371` and additionally
imports `CMod32Bridge.lean` to upgrade Agent 11's full original-machine
halting equivalence by explicitly adding `j%32 != 16`.

CI verification is tracked in [workflow runs](https://github.com/FlareZ123/bb6/actions/workflows/agent21-c-source-bridge.yml).
Only update the CI verification status after checking success and the
axiom audit from that run.

This excludes the entire `j=16 (mod 32)` reset line but does **not**
prove the original Machine C nonhalting or determine BB(6).
