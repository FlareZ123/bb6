# Raw10 base34 rectangle 12: exact domain cover

**Status:** complete computational certificate candidate, final exhaustive proof assembly pending. Lean 4.36.0-rc2 checked the source-index match, generic checker soundness, all 60 hard block-FAR certificates, and the composed E0=0/3/12/18 subcover locally against accepted original-source dependency objects. The four checked branches cover 39,062,500 tables at weighted bound 205. The conditional 29/27 local Raw10 residual consumers also passed; they still require the complete Box12 bound (and the 27 variant requires separate Box16/17 bounds).

The target is precisely `raw10Remainder[12]!` in the original base34 rectangle list. Its code vector is [8,25,11,11,17,13,11,25,25,25,25,25], where 25 is unassigned, 0 is halt, and ordinary instructions are 1+4*state+2*write+right. E0 (index 8) is restricted to [0,3,4,12,18,20,21,22,23,24]; the other five holes permit all 25 values. Thus the rectangle contains 10*25^5 = 97,656,250 tables.

First-hole branching produces 5982 split nodes and 143554 terminal leaves: 65548 left rays, 23429 right rays, 21371 cycles, 22823 last-hole decisions, 5982 halts and 4401 initially open leaves. Bit FAR and sparse ngram extensions resolve 4341 of these; block FAR resolves the remaining 60 (55 width-three, five width-two), all individually kernel-checked with exact-table dispatch in Box12External. The computed maximum ordinary bound including halt is 200; weighted target 205 allows at most five initial blank-delay steps.

## Checked interfaces

- [PackedFinite.lean](PackedFinite.lean) proves the natural-number tape encoding, exact finite and bounded run simulation, packed translated-cycle soundness, halt/last-hole equivalence, and domain-restricted array-tree soundness. It uses only standard axioms.
- [Box12FourE0.lean](Box12FourE0.lean) proves the checked four-branch bound with explicit original-source membership.
- [Raw10RefinedBox12Cut.lean](Raw10RefinedBox12Cut.lean) proves conditional 29/27 consumers. [Raw10RefinedBox12.lean](Raw10RefinedBox12.lean) is the final consumer once the full Box12 theorem passes.

## Reproduce

1. Use Lean 4.36.0-rc2. Obtain the accepted dependency closure from [run 45906154912, artifact 15158192432](https://github.com/FlareZ123/bb6/actions/runs/45906154912/artifacts/15158192432), zip SHA256 `783b0daa58f8d42e6bc49bb29b6cb743b70acc6070337faa2686aa02379c55e9`. The olean directory within it is `tmp/a49-raw10-box6-probe`.
2. Run `python3 unpack.py /absolute/workdir`. The uncompressed source JSON SHA256 is `7f35bfdde7e0e64231af52ebc093bb45b4a3bd9b3cb7e2e573c2ff088f73edff`.
3. In the workdir run `bash reproduce.sh /absolute/repo /absolute/dependency-olean-directory` for the original checker. For the packed checker use the [manual workflow](../../.github/workflows/agent48-raw10-box12.yml), which runs generation once, compiles the ten E0 partitions independently, and then joins their actual theorems. The initial dispatched [run 46112001673](https://github.com/FlareZ123/bb6/actions/runs/46112001673) is pinned to commit c1a4058dbd45ba9aad3e943ddc110ef1182752b0.
4. Target theorem: `BB6.Agent48Box12.box12_weighted` in generated `tree/Box12Cover.lean` (211 generated source modules). The final job additionally checks the unconditional-on-Box12 local 29/27 consumers. Require successful final compile with standard axioms. Discovery is not trusted by the proof.

The sparse representation completes all hard leaves; the outstanding issue is the exhaustive branch composition. No global BB(6) bound or Canonical40 reduction is asserted.
