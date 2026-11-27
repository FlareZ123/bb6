# Raw139 E0=1RA: complete computational candidate, parent source audit pending

Parent: `[7,24,11,24,14,24,24,16,3,11,24,24]` (six initially unspecified rows). The fixed parent candidate has weighted bound **529714**. This is **not** a completed parent Cover or a global BB(6) decision.

## Discovery outcome

The original 450-step, DFA-size-2 prefix-sharing replay produced 27113 split nodes and 623600 ordinary leaves: 429438 cycles, 125736 last-hole leaves, 60203 FAR leaves, and 8223 unclassified partial tables. Fixed width-two, three and four Block-FAR witnesses classify 8159 of those opens. Of the remaining 64, 61 are finite last-hole traces, 2 need a further split, and H4620 is an infinite binary-growth family. The two extra splits have 48 ordinary children: 46 Block-FAR witnesses and 2 finite last-hole traces. Thus the proposed final tree has 27115 splits and **623646 leaves**:
- 429438 cycle witnesses
- 125799 finite last-hole witnesses
- 60203 FAR witnesses
- 8205 Block-FAR witnesses
- 1 exact all-completion nonhalting lemma

No computationally unclassified leaf remains. These counts describe a *candidate* partition. The parent theorem requires actual source proof acceptance.

## Mathematical results already checked locally

- [H4620.lean](H4620.lean): all-completion NeverHalts and arbitrary-B weighted Cover, with explicit binary carry and growing-epoch invariant. See [derivation](H4620-invariant.md).
- Eight long last-hole traces (original open identifiers 576, 1286, 5577, 6103, 6137, 6573, 6852, 7900) have locally compiled sharded packed proofs at bound 529714, using original PackedAudit semantics and kernel-only decisions. H6573 has exact prefix 529708, 133 segments and one remaining undefined transition at A1. The other seven have all been compiled with the generator's proof template. The eight proofs are for their literal tables, not the parent.
- The sparse Block-FAR models for widths two, three and four were specialized from the previous source-checked wide sparse semantics and compiled locally. All 15 width-four witnesses also passed locally using the earlier width-four sparse implementation, including reflected witnesses. The new sparse model's reflected batches have accepted samples, but the large batches timed out under the local per-call limit; no blanket acceptance claim. The parent pipeline will independently check the actual emitted witnesses.

Local Lean 4.36.0-rc2 and original artifact 15166454197's semantic dependency objects were used. All audited proofs above used only propext, Classical.choice, Quot.sound; no sorryAx or native_decide. A fresh original-source closure of the entire parent is pending.

## Reproduction and source gate

- `candidate.json.xz.b64`: complete fixed witness recipe assignment, exact open-table order hash, late traces, child split entries, and H4620 match; decode xz/base64 (JSON SHA-256 b31b9a1b4e6f76e1141d7e50add8f5682bd54d083eb74ad62552eb1c28df926d).
- `prepare.py`: materialize the fixed graft from the original replay, checking literal tables and the two newly queried holes; no new search.
- `sparse-models.json.xz.b64`: six exact locally compiled source modules for widths 2–4.
- `generate-parent.py`: existing package6 tree emitter with sparse certificate representation, reflection and weighted external-leaf transformer.
- `emit_late.py`: kernel-only packed trace generator and balanced joins.
- `pipeline.sh`: prepare, twelve disjoint root-child shards, final composition. Original-source certification dispatched [45954243655](https://github.com/FlareZ123/bb6/actions/runs/45954243655) at source commit 5b8df3daac435ebfffe86c8870922e6157828cdd. The dispatch is queued, not success.

Target interface: `BB6.Agent48Raw139E0OneRA.all_completions_weighted`, exact table above, WeightedBound 529714. On success only, consume exact normalized Raw139 E0=1RA (row code 3); retain every other obligation. No global roster subtraction is justified yet.
