# Compact forward reset-path certificate: #746 fatal indices through 10,000

**Original-source accepted (24 November 2026):** no height `4*2^n-n-4` for any `n≤10000` is reachable from the blank-root reset height 2. The arithmetic certificate uses ordinary kernel `by decide`, and `OriginalGate10001.lean` now compiles against the unmodified upstream six-state machine at Cryptids revision `c86f15861709b76042998c5211c7b2f83991621b`. The raw-machine halting equivalence requires `n≥10001`, with `n mod 6∈{4,5}`. This is a bounded fatal-index exclusion; the unbounded family and #746 remain open.

## Mathematical mechanism

For a valid even or odd reset edge from h at level k, the complete source inequalities give

    fatal(k) < h < fatal(k+1),  fatal(n)=4*2^n-n-4.

Since fatal is monotone, every fatal height is a dead end in the reset graph. The exact grammar is deterministic (the source intervals force k; parity distinguishes even/odd; unique factorization 2^t*d with d odd forces the odd valuation) and strictly increasing. Consequently, a single accepted path from 2 to z>fatal(N) excludes every fatal(n), n≤N, at all path lengths. No inverse fan traversal, per-index root test, or per-transition fatal-membership test is required.

A Python generator proposes just (k,t) for each reset and checkpoint endpoint heights. Lean computes and checks each proposed edge against the complete grammar and verifies the block endpoint by kernel reduction. Only successful paths can satisfy the certificate; an erroneous candidate cannot be silently interpreted as a halt. The checker does not rely on the generator's candidate-level selection being complete.

## Reproduction and acceptance

In this directory, with Lean 4.36.0-rc2:

    export LEAN_PATH=.
    lean -o ResetBlockCore.olean ResetBlockCore.lean
    python3 generate_reset_blocks.py --bound 10000 --chunk 128 --output Cert10000.lean
    lean -o Cert10000.olean Cert10000.lean
    lean -o Bound10000.olean Bound10000.lean

The locally completed run generated 12,884 successful resets in 101 blocks, endpoint bit length 10,003, 312,970 bytes of generated Lean source. Certificate compilation took about 14 seconds in the local container. The certificate is generated deterministically instead of checked in as a large source file. Core and bound were compiled cleanly; the generated prefix theorem depends on propext and the exclusion theorem on propext and Quot.sound. A 50,000-index attempt with 512-reset blocks did not complete within the local tool timeout; it is not an accepted stronger bound.

The original-source run [45336867924](https://github.com/FlareZ123/bb6/actions/runs/45336867924), research commit `3cdfd2ce44bcc47d68466cbbb17566d021b04b51`, built unmodified upstream with Lean 4.35.0-rc4 and accepted the complete adapter. Its log reports no axioms for `edge_iff_source`; `[propext, Quot.sound]` for `no_fatal_through_10000`; and `[propext, Classical.choice, Quot.sound]` for both `source_no_fatal_through_10000` and `original_machine_halts_iff_surviving_10001`. No `sorryAx` or native-decision axiom occurs in those profiles.

Next: use batched same-level even resets and sharded certificates for a stronger finite bound, and develop an all-time invariant for the resulting accelerated level-entry map. The existing original-source theorem now supersedes OriginalGate268 for the bounded gate.
