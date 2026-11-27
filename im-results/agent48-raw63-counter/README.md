# Raw residual 63: exact five-hole counter closure

Status: **complete original-source parent Cover accepted; sharpness locally kernel-checked**. Parent
`1RB---_1RC1LA_0RD---_1LD1RE_---0LB_------`, canonical raw residual 63,
B1 divergence at path depth 5. The normalized weighted bound is exactly 358.

The existing first-hole enumerator (Agent 2) produces 1,342 splits including
the root, 22,989 cycle leaves, 7,105 last-slot leaves and 773 open leaves.
The raw mass is 9,765,625 = 25^5. The open list SHA-256 is
`700d61266df4fa9fb38a6086df1f10a877397e6ac5288c11aeee916b9f5d8c18`.

All 773 open leaves have certified witnesses:
- 710 FAR, 48 one-block sweep, 5 two-block sweep, 1 long-period sweep;
- 9 recursive binary-counter families: 98, 99, 100, 101, 102, 103, 104, 205, 679.

The new carry recurrence uses zero block Z=0001, one block O=0101, and an
arbitrary untouched suffix S. Fixed-padding machines have a carry
`O^n Z S -> Z^n O S`. For growing padding, D has left list
`0000 (00)^k 1 O^n Z S`, empty right list, and the carry increments k.
The outer return from all-ones has positive cost and inserts one leading one
and n zeros; normalization by induction on n closes the invariant. No
simulation cutoff is a nonhalting claim. A long 12-cell sweep closes leaf 42.

`Agent48CounterCore.lean` proves the normalization and positive-progress
combinators. `emit_counter.py` emits finite phases (rfl), sweep induction,
word rotations, and complete original-source nonhalting theorems for the
nine machines. The local Lean 4.36.0-rc2 preflight checked the exact zipper
transition and sweep definitions plus the counter inductions and all nine
macro families; the full original-source import chain passed the shared manual sharded coverage workflow (below). Local git checkout was blocked by DNS.
The complete audit reuses Agent 10's generator, with raw63 spec in its
specs.json. The bridge uses the exact sameTable gate on the canonical roster.

Reproduce:
```sh
python im-results/agent13-coverage/unpack.py
python im-results/agent31-three-hole-tnf/generate_sweeps.py
python im-results/agent31-three-hole-tnf/generate_four_hole.py
python im-results/agent48-raw63-counter/emit_counter.py
python im-results/agent10-tnf-multipump/generate.py 63
python tools/lean_compile_closure.py --workdir /tmp/a48-raw63 --jobs 4 im-results/agent48-raw63-counter/Raw63RosterBridge.lean
```

The source closure and parent audit are accepted. Do not remove Raw63 from the current canonical roster until exact membership and the current fixed-score consumer compile.

## Original-source checkpoint

Run [45508818219](https://github.com/FlareZ123/bb6/actions/runs/45508818219) compiled Agent48CounterCore and all nine original-source NeverHalts theorems, each with propext and Quot.sound only. The complete certificate build did not finish: runner shutdown (exit 143) interrupted Raw63Kid05. This interruption is superseded by the accepted independent sharded audit.

## Complete parent and exact threshold

The independent six-shard audit [45948590270](https://github.com/FlareZ123/bb6/actions/runs/45948590270) succeeded. Its parent artifact [15176425936](https://github.com/FlareZ123/bb6/actions/runs/45948590270/artifacts/15176425936) (SHA256 `87a813136a63d929a6c0fe154925d747a0f4a7759abb9bf1b9aa3c3adbc9e2a5`) compiled 81 project modules at pinned source revision `b8267e0c61cf97fafefb257edf286907c0b3baf7`. The final log explicitly accepts `BB6.Agent2Raw63.parent_eq_literal`, `parent_cover`, and `literal_cover`, the last two with only `[propext, Classical.choice, Quot.sound]`.

[Raw63Attainment.lean](../agent2-raw63-shards/Raw63Attainment.lean) constructs the compatible full machine
`1RB0LA_1RC1LA_0RD0RF_1LD1RE_HHH0LB_0RC1LA`.
It takes 357 live transitions from blank and halts at E0, with allowed blank offset zero. The accepted upper bound and this witness prove
`(∀ m, compatible literalParent m → WeightedBound B m) ↔ 358 ≤ B`.
Lean 4.36.0-rc2 locally compiled the exact new source against the downloaded, digest-checked 81-module accepted artifact. The threshold theorem uses only the three standard axioms; the halting witness uses only propext. This local threshold proof is not itself a new CI run and does not remove a global roster entry. The parent Cover at 358 is ready for the current Canonical53-lineage consumer.
