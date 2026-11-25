# Raw123: complete source-accepted six-hole parent bound

The literal parent is `1RB---_1RC---_0RD---_1LD1RE_---0RF_------` (E1=0RF), with first undefined query F1 at step 7. **Complete:** `BB6.Agent7Raw123.raw123_cover (B : Nat) (hB : 10000 ≤ B) : Cover (WeightedBound B) p123` is accepted in [run 45700813110](https://github.com/FlareZ123/bb6/actions/runs/45700813110), artifact `raw123-final` 15062767168. See the [mathematical result](../../results/2026-11-25-raw123-parent-cylinder-bound-agent7.md). No exact parent maximum is asserted.

## Proof construction

- `generate.py`, `generate_growth.py`, `growth.b64`, `special.txt`, and `extra_bank.txt` reconstruct the weighted TNF cut without searching for new witnesses. The cut has 40 exact retained entries and every other completion is bounded by 10000; the cut source audit is 45599211107.
- `build_ngrams.py` and `build_blocks.py` reconstruct the 19 and 21 exact nonhalting certificates. Parts 0–4 of 45599642959 succeeded; its cancelled part 5 was replaced by the accepted compact sparse certificate in 45699207447. All six artifact groups contain their compiled source dependencies.
- `merge_final.py` checks the six exact part names, requires a matching compiled object for every Lean source, rejects differing duplicate source bytes, and merges the accepted cut and residual parts. `Raw123ResidualClosure.lean` checks that every residual table matches an explicit original-machine nonhalting theorem and closes the parent.
- The final assembly uses `.github/workflows/agent7-raw123-residuals.yml` with parent=123, cut_run=45599211107, residual_run=45599642959, supplement_run=45699207447. This succeeded after correcting the reserved identifier in the final wrapper. Do not regenerate the accepted 587-module closure unnecessarily.
- Width-seven support-aware block-FAR proof and compact emitter are in `../agent13-block-far/ActiveSparseFAR.lean` and `emit_active.py`. Local data-only compilation improved from 58.48s to 5.23s; this timing is not the full source verification time. The final full source job passed.

## Consumer

The accepted parent is `BB6.Agent7Raw123.p123`; the bound is 10000, so use a mixed-bound target (B\ge10000), not the obsolete requirement that every new parent have bound 7014. Verify exact membership of this literal parent in the current canonical roster and consume `raw123_cover B hB` at the target. The named theorem does not itself reduce the global accepted roster count.
