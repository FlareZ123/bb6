# Singleton-projection BlockFAR search for the raw10 complement

This is a residual-directed experiment against the exact 34 boxes left by
`im-results/agent49-box-complement/Raw10Encoded.lean`.

## Mathematical reduction

Each box is a product of allowed transition-code domains for the 12
state/symbol slots. Its singleton projection fixes only slots whose domain is
a singleton ordinary transition. Every other slot is left undefined, including
a singleton halt slot. Consequently every total machine fitting the box is a
completion of the projected partial table.

The existing Agent13 BlockFAR soundness theorem proves that every completion
of a generated partial table runs forever when its certificate succeeds.
Therefore a successful certificate for a singleton projection proves the
whole box safe. This is a sufficient condition only; a failed generator run
does not imply that the box contains a halting machine.

The projection uses the existing stable `Fin 25` encoding:
- `0`: wildcard/halt, left undefined in the projection;
- `1..24`: ordinary moves in state-major order, matching
  `BB6.Agent31ThreeHole.allMoves` and the standard table strings.

## Exact box reconstruction

`search.py` parses the 66 encoded cylinders (65 side witnesses plus the
q_i(2800,100) held cylinder) and reproduces the first-mismatch subtraction
from `BB6.Agent49Box.subtractMany`. It checks:
- exactly 34 remainder boxes;
- total remainder mass 90,890,091,604,975.

The disjointness and exactness of the decomposition are already proved in
`BoxComplement.lean`; the script is an independent reproducibility check,
not a replacement for that theorem.

## Running

From the repository root:

```bash
python im-results/agent17-raw10-box-far-search/search.py
python im-results/agent17-raw10-box-far-search/search.py --generate --min-fixed 6
python im-results/agent17-raw10-box-far-search/search.py --generate --compile --min-fixed 6
```

The search calls the existing `im-results/agent13-block-far/generate.py`
without modifying it. Successful candidates are generated in the output
directory (default `.tmp/agent17-raw10-box-far` (inside the checkout, so the Lean closure scanner can see generated modules)). With `--compile`, each
candidate is checked by `tools/lean_compile_closure.py` in an isolated
work directory. Only a successfully compiled certificate may be consumed by
a future `Raw10BoxBridge` refinement.

No box is counted as closed merely because the generator produced a file.

Optional `--include-cycle` and `--include-halt` flags subtract Agent50's
`Raw10Box8Cycle` and `Raw10Box0Halt` tables before generating projections.
Use them only after the corresponding source certificates have passed kernel
CI. In these auxiliary rows, `25` is a sentinel for a forced halt, while
`0` continues to mean wildcard. The expected replay checks are:
- base: 34 boxes, mass 90,890,091,604,975;
- cycle: 40 boxes, mass 90,890,091,604,350;
- halt: 35 boxes, mass 90,737,503,714,350;
- cycle + halt: 41 boxes, mass 90,737,503,713,725.

These are finite replay checks; formal exactness comes from the corresponding
`remainder_exact` and disjointness theorems in the source consumers.
