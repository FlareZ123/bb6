# Raw residual 63: five-hole counter closure candidate

Status: **candidate complete; original-source Lean audit pending**. Parent
`1RB---_1RC1LA_0RD---_1LD1RE_---0LB_------`, canonical raw residual 63,
B1 divergence at path depth 5. The normalized weighted bound candidate is 358.

The existing first-hole enumerator (Agent 2) produces 1,342 splits including
the root, 22,989 cycle leaves, 7,105 last-slot leaves and 773 open leaves.
The raw mass is 9,765,625 = 25^5. The open list SHA-256 is
`700d61266df4fa9fb38a6086df1f10a877397e6ac5288c11aeee916b9f5d8c18`.

All 773 open leaves now have candidate witnesses:
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
macro families; the full original-source import chain is to be checked by
the shared manual coverage workflow. Local git checkout was blocked by DNS.
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

Do not remove raw63 from the accepted canonical roster until the full
source closure, raw63 audit, and exact roster bridge compile.
