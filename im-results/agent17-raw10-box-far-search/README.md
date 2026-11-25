# Singleton-projection BlockFAR search for the raw10 complement

## Status (2026-11-25)

The generic singleton-projection soundness theorem and exact source-box correspondence are kernel-checked. The complete search over the 34 exact source residual boxes produced **zero** certificates with the existing Agent13 finite-exit generator. This is a method-specific negative result, not a decision about any box.

Full per-box projections, completion masses, and generator failure keys are in [RESULTS-2026-11-25.md](RESULTS-2026-11-25.md).

## Mathematical reduction

Each box is a product of allowed transition-code domains for the 12 state/symbol slots. Its singleton projection fixes only slots whose domain is a singleton ordinary transition. Every other slot is left unassigned, including a singleton halt slot. Consequently every total machine fitting the box is a completion of the projected partial table.

The theorem in `BoxSingletonProjection.lean` proves that a valid BlockFAR certificate for this projection implies every total completion fitting the box is nonhalting (and inherits the corresponding `WeightedBound`). A successful certificate would therefore close the whole box. A failed generator run proves nothing.

The projection uses the stable `Fin 25` encoding:
- `0` in an encoded cylinder row means wildcard; the domain value 0 itself is halt and is left unassigned in the projection;
- `1..24` are ordinary moves in state-major order.
In the projection strings, `---` means unassigned/wildcard, not an assigned halt.

## Exact source correspondence

`Raw10EncodedSourceBridge.lean` kernel-checks the bridge between the encoded search and the actual source remainder. It proves:
- the 66 encoded rows are exactly the 65 filtered source side witnesses plus the authentic q_i(2800,100) held table;
- both source and encoded remainders have 34 boxes;
- every encoded box at its original index is pointwise equal to the corresponding `Raw10BoxCore.raw10Remainder` box.

The existing `Raw10BoxCore` source theorems establish exactness and disjointness of the source remainder. The new bridge compiled 51 project modules in CI run [45702115754](https://github.com/FlareZ123/bb6/actions/runs/45702115754); the new theorem axiom profiles contain only `propext` and `Quot.sound`, with no `sorryAx` or `native_decide`.

The generic theorem closure compiled 53 project modules in CI run [45702721207](https://github.com/FlareZ123/bb6/actions/runs/45702721207). Its axiom profiles contain only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`), with no `sorryAx` or `native_decide`.

## Search result

The full run tested all 34 boxes with at least two singleton ordinary moves, preserving original indices and trying larger singleton projections first. Total product-domain mass was **90,890,091,604,975**. The generator emitted **0** certificates; consequently **0** candidates were compiled.

Every miss reports `RuntimeError: abstract row not a finite exit`, in one of four abstract-state patterns. The current generator cannot close these projections; the diagnostic does not distinguish an unassigned transition from a safe internal cycle. Do not rerun the same scan or interpret these errors as machine decisions.

See [RESULTS-2026-11-25.md](RESULTS-2026-11-25.md) for the complete per-box table.

## Reproduction

From the repository root:

```bash
python im-results/agent17-raw10-box-far-search/search.py
python im-results/agent17-raw10-box-far-search/search.py --generate --compile --min-fixed 2 --max-boxes 34 --rank-promising --compile-timeout 180 --jobs 4
```

The search calls the existing `im-results/agent13-block-far/generate.py` without modifying its proof algorithm. Successful candidates are generated in the output directory (default `.tmp/agent17-raw10-box-far`). With `--compile`, each candidate is checked by `tools/lean_compile_closure.py` in an isolated work directory. The script prints the exact exception and diagnostic tail for every miss.

The existing manual workflow target `weighted-tnf-raw10-box-ranked-search` runs the Lean generic proof check and the full 34-box search. It is in `.github/workflows/agent13-coverage.yml`; no new workflow was created.

Optional `--include-cycle` and `--include-halt` flags subtract Agent50's `Raw10Box8Cycle` and `Raw10Box0Halt` tables before generating projections. Use them only after the corresponding source certificates have passed kernel CI. In these auxiliary rows, 25 is a sentinel for a forced halt, while 0 continues to mean wildcard. The expected replay checks are:
- base: 34 boxes, mass 90,890,091,604,975;
- cycle: 40 boxes, mass 90,890,091,604,350;
- halt: 35 boxes, mass 90,737,503,714,350;
- cycle + halt: 41 boxes, mass 90,737,503,713,725.

These optional partitions require their own source-consumer proofs before their mass can be counted globally.

## Next direction

Do not repeat singleton projection. A more promising method is domain-preserving/set-valued BlockFAR, which checks every allowed transition at a visited slot and can admit safe internal cycles. Coordinate with Agent49 before targeting boxes already covered by its box7, box6, and 18–24 work, and with Agent50 before touching box8. Box17 is a possible next target, pending deconfliction.

This is intermediate research only. No global BB(6) upper bound is established; keep these artifacts in `im-results/`, not `results/`.
