# Compact forward reset-path certificate: #746 fatal indices through 10,000

**Established locally in Lean 4.36.0-rc2:** no height `4*2^n-n-4` for any `n≤10000` is reachable from 2 in the arithmetic Edge relation, whose definition is identical to `CascadeResetInverse.ResetParent`. The checker uses ordinary kernel `by decide`, not native_decide, and the final theorem has exactly [propext, Quot.sound]. The separate original-source adapter is written but must be compiled against the pinned upstream dependencies before reporting the raw-TM theorem as accepted. This is a bounded fatal-index exclusion, not a decision of #746.

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

`OriginalGate10001.lean` contains the definitional grammar bridge, conversion of source ResetChain to Path, and the strengthened original raw machine gate (10001≤n). **This adapter is not yet source-compiled.** Existing source-accepted OriginalGate268 remains the maintained original-machine bound until this adapter passes its actual upstream compile and axiom audit.

Next: run the focused existing original-source workflow target for the adapter; after acceptance, use block-size tuning and sharded certificates to extend the bound without repeated inverse enumeration. The all-index existential remains open; the bounded certificate is useful for finite pruning but does not replace an all-time rooted invariant.
