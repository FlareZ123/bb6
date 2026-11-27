# Reproducible Raw41 source-checked certificates

These JSON fixtures and compact FAR codes are source material for Lean 4.36.0-rc2 proofs, **not axioms**. Original finite traces and FAR automata are reconstructed by `close_candidate.py` and the original source `gen_children.py`. The original Lean `Agent46AutoPump.check` checks symbolic sweep certificates. A certificate is accepted only after the source-checker CI compiles each resulting `Raw41NewNNNClosed` theorem.

## Raw41 child084: mixed regular / affine proof

The original exact 49-open-leaf child had 46 ordinary FAR certificates. Original open leaf22 is a source-reconstructed 6-DFA certificate `1012134545555`. Leaves8 and14 are the two stored exact symbolic pumping fixtures:

- [leaf08](child084-leaf08-autopump.json): entry45, one shared repeated-block growth unit, identity trace cost `10n + 57`.
- [leaf14](child084-leaf14-autopump.json): entry18, one shared repeated-block growth unit, identity trace cost `40n + 77`.

The complete finite proof tree is regenerated from a clean checkout by:

```sh
python3 im-results/agent36-raw41/close_candidate.py \
  --index 84 --dfa 5 --time 900 \
  --far-override '22:1012134545555' \
  --auto-json im-results/agent36-raw41/certificates/child084-leaf08-autopump.json \
  --auto-json im-results/agent36-raw41/certificates/child084-leaf14-autopump.json \
  --out .tmp/raw41-rebuilt-084
```

The original-source kernel confirmation was [CI run 46082024854](https://github.com/FlareZ123/bb6/actions/runs/46082024854) (only standard axioms, no `sorry` or native computation). The witness bytes are checked by `Agent46AutoPump.check` and `canonicalCheck`; these certificates themselves do not need an external solver after they are stored.

## Other added original-source FAR certificates

| Canonical child | Original open-index : FAR code | Role |
|---|---|---|
| 081 | `41:10152634177777777` | novel 8-DFA nonhalting leaf, checked CI 46081314280 |
| 083 | `2:001324666656166`, `73:101234354446441` | two 7-DFA search witnesses |
| 092 | `1:0011253044441`, `19:001423454446434`, `21:0014243335343`, `98:0010235410104` | four source-reconstructed witnesses |
| 116 | `148:001524356525501`, `149:0014243405555`, `150:1012344514401`, `151:1012355415555`, `162:001243333253601`, `178:1012433335101` | six source-reconstructed witnesses |

Use comma-separated values with `close_candidate.py --far-override '<values>'`; all codes are independently tested by the original `generate_two.far` and thereafter by Lean. Prior child125 uses `--late '2:1423:9' --min-bound 1500` (the original 85-leaf tree has 84 FAR certificates); it is a finite computation, not a FAR witness.

The main research record is `im-results/agent36-raw41/README.md` and the academic result index is `results/README.md`. All source tables and fixure data retain the original 6×2 transition semantics. Any summary claiming a global BB(6) upper bound without discharging the remaining global roster is invalid.
