# Compact forward reset-path certificate: #746 fatal indices through 50,000

**Original-source accepted (24 November 2026):** no height `4*2^n-n-4` for any `n≤50000` is reachable from the authentic blank-root reset height 2. [OriginalGate50001.lean](OriginalGate50001.lean) gives the exact remaining halting gate n≥50001 and n mod6∈{4,5}. This bounded exclusion does not decide the infinite residual family or BB(6).

## Mathematical mechanism

For each successful reset edge at level k, fatal(k)<h<fatal(k+1), where fatal(n)=4*2^n-n-4. The complete reset grammar is deterministic and strictly increasing, and fatal heights have no outgoing edge. Consequently an authenticated successful path from 2 to z>fatal(N) excludes every fatal(n), n≤N, at every path length.

[EvenBatch.lean](EvenBatch.lean) proves the soundness of checking r consecutive even resets at level k by endpoint equations h+2^r*d=W, u+d=W, W=8*2^k+k, and the endpoint band inequalities. The intermediate edges follow inductively from the full ResetParent grammar. A macro witness specifies the level, length of an even run, and the optional subsequent odd valuation. The fast checker replaces division by powers of two with shifts; its equality to the ordinary checker and path soundness are Lean theorems. Independent bounded-size shards are checked by kernel reduction and composed into a balanced path proof. The untrusted Python generator proposes witnesses only.

## Reproduction

Lean 4.36.0-rc2, from this directory:

    export LEAN_PATH=.:shards50000
    lean -o ResetBlockCore.olean ResetBlockCore.lean
    lean -o EvenBatch.olean EvenBatch.lean
    python3 generate_sharded_macro.py --bound 50000 --chunk 64 --shard 32 --output shards50000
    while IFS= read -r m; do lean -o "shards50000/$m.olean" "shards50000/$m.lean"; done < shards50000/modules.txt

The certificate contains 64,984 successful resets, 32,180 macro records, 16 shards, and an endpoint of bit length 50,004. Both `certified_macro_prefix_50000` and `no_fatal_through_macro_50000` depend only on propext and Quot.sound.

The full original-source run [45338279095](https://github.com/FlareZ123/bb6/actions/runs/45338279095), research commit `47f2c48d47a8973189284c8367c769fa7987b81c`, builds unmodified Cryptids revision `c86f15861709b76042998c5211c7b2f83991621b` with Lean 4.35.0-rc4. Its accepted adapter theorem `Agent10Raw746.original_machine_halts_iff_surviving_50001` and `CascadeResetShield.source_no_fatal_through_50000` have precisely [propext, Classical.choice, Quot.sound]. The grammar equivalence has no axioms. No sorryAx or native-decision axiom appears.

The preceding 10,000 bound used 12,884 individual witnesses and is independently accepted in [CI 45336867924](https://github.com/FlareZ123/bb6/actions/runs/45336867924), research commit `3cdfd2ce44bcc47d68466cbbb17566d021b04b51`. It is superseded by 50,000. The unbounded proof objective is an invariant of the actual level-entry orbit; the existing all-index level macro and alternating-exit results in [the bitsweep dossier](../agent7-746-bitsweep/README.md) are the appropriate starting point. Extending finite cutoffs alone cannot establish nonhalting.
