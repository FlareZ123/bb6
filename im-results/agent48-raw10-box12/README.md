# Raw10 base34 rectangle 12: domain-restricted cover

**Current status (2026-11-28): complete computational candidate; final exhaustive Lean composition still in progress.** The source-index match, generic checker soundness, E0=0/3 branches, and all 60 hard block-FAR leaf certificates have been checked by Lean 4.36.0-rc2 against accepted Raw10 dependency objects. Do not use the full-parent theorem until its remaining generated shards and root pass.

The target is precisely `raw10Remainder[12]!` in Agent49's original base34 rectangle list, not a guessed refined-frontier ordinal. Its code vector is [8,25,11,11,17,13,11,25,25,25,25,25], where 25 is unassigned, 0 is halt, and ordinary instructions are 1+4*state+2*write+right. E0 (index 8) is restricted to [0,3,4,12,18,20,21,22,23,24]; the other five holes permit all 25 values. Thus the rectangle contains 10*25^5 = 97,656,250 tables.

First-hole branching produces 5982 split nodes and 143554 terminal leaves: 65548 left rays, 23429 right rays, 21371 cycles, 22823 last-hole decisions, 5982 halts and 4401 initially open leaves. Bit FAR and sparse ngram extensions resolve 4341 of these; the remaining 60 are resolved using block FAR (55 width-three, five width-two), all individually kernel-checked with exact-table dispatch in Box12External. The computed maximum ordinary bound including halt is 200; the weighted target is 205 (allowing at most five initial blank-delay steps). The E0=0/3 subcover already certifies 19,531,250 complete tables.

## Reproduce

1. Use Lean 4.36.0-rc2. Obtain the accepted dependency closure from [run 45906154912, artifact 15158192432](https://github.com/FlareZ123/bb6/actions/runs/45906154912/artifacts/15158192432), zip SHA256 `783b0daa58f8d42e6bc49bb29b6cb743b70acc6070337faa2686aa02379c55e9`. The olean directory within that archive is `tmp/a49-raw10-box6-probe`. Its source modules derive from the existing Agent49 Box6/Raw10 closure.
2. Run `python3 unpack.py /absolute/workdir` from the repository checkout. The uncompressed source JSON SHA256 is `7f35bfdde7e0e64231af52ebc093bb45b4a3bd9b3cb7e2e573c2ff088f73edff`. The two chunks are plain base64 without trailing newlines.
3. In the workdir run `bash reproduce.sh /absolute/repo /absolute/dependency-olean-directory`. This regenerates all search witnesses, adapts the prior Agent48 block-FAR discovery and sparse models, and checks every finite decision with `decide +kernel`, then applies the source soundness theorems. Discovery is not trusted by the proof.
4. The target theorem is `BB6.Agent48Box12.box12_weighted` in generated `tree/Box12Cover.lean`. The generated tree currently has 211 source modules. Require successful final compile and standard-axiom-only `#print axioms box12_weighted` before integration. No new global BB(6) bound or Canonical40 reduction is asserted here.

The dense block verifier was impractical for these witnesses; the sparse representation has already completed all hard leaves. This package is under im-results pending final source acceptance.
