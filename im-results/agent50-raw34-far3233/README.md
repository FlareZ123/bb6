# Raw34 pair endgame (D1=0LF, F0=0LD)

For the existing 3,233-row hard census, the four-state FAR search found 3,065 hits and 168 misses. A local continuation found 159 of those misses with five-state FAR, and eight of the remaining nine with six-state FAR. The unique last miss is census ID 2071, code row [21,19,22,12,11,1,16,7,18,20,5,14]; C1 is a physical HALT, not an unspecified transition.

The last machine has a symbolic growth proof, not merely a simulation cutoff. At step 57 its state is C and its zipper is left (including current) 01110110 followed by (11)^(n+1), with empty right, for n=0. The next checkpoint increases n by one and takes 12*n+43 transitions. The five phases cost 16, 2*(n+2), 2, 5*(2*n+3), and 6. Consequently checkpoint n occurs at 6*n^2+37*n+57. See Raw34M2071Growth.lean.

The full `never` theorem in `Raw34M2071Growth.lean` was compiled locally with Lean 4.36.0-rc2 against byte-identical original Frontier, Symmetry, RootShift, SparseZipper and SweepPumping. All six file Git blob hashes matched remote; axioms for `never`: [propext, Quot.sound]. FAR hits are search witnesses pending FastFAR checks. The 3,233 and 168 predecessor covers likewise must pass original-source verification before the pair parent can be called closed. No global Cover count is changed here.

Next: compile the combined original-source target in coordination with the existing Raw34 pair owners. Do not duplicate the global Raw47 consumer.


## Reproduce the endgame

With the existing hard3233.txt and far4.jsonl (all original census IDs in order), compile the existing agent50-raw34-plan/far.cpp to far, and run:

```bash
python - <<'PY'
import json
from pathlib import Path
rows = Path('hard3233.txt').read_text().splitlines()
misses = [x['id'] for x in map(json.loads, Path('far4.jsonl').read_text().splitlines()) if 'd' not in x]
Path('hard168.txt').write_text('\n'.join(rows[i] for i in misses)+'\n')
PY
./far 5 < hard168.txt > far5.jsonl
python - <<'PY'
import json
from pathlib import Path
rows = Path('hard3233.txt').read_text().splitlines()
misses = [x['id'] for x in map(json.loads, Path('far5.jsonl').read_text().splitlines()) if 'd' not in x]
Path('hard9.txt').write_text('\n'.join(rows[i] for i in misses)+'\n')
PY
./far 6 < hard9.txt > far6.jsonl
python generate_close_168.py --hard hard3233.txt --far4 far4.jsonl --far5 far5.jsonl --far6 far6.jsonl --output generated
```

The generator ran locally, producing 14 source shards and Raw34FAR168Closed.lean.
Ordered 168-row SHA256: e5a91a6700e3e2027c85923c8b6661ff8cee6e6167ad0903b525ed538ee792f9.
The final theorem is BB6.Agent50Raw34FAR168Closed.cover : Cover (DecidedBelow 128) BB6.Agent40Raw34PairD1LF_F0LDDepth6Data.parent. Its proof requires all original dependencies (including the 3233-to-168 predecessor), checks every FAR witness with FastFAR, proves the last row agrees with the growth machine, and proves literal list equality with the predecessor misses in Lean. The output is not yet source-accepted.

## Stronger sparse-cylinder result (source-checked locally)

Local Lean 4.36.0-rc2 compiled all 83 certificate shards and the aggregate `BB6.Agent50Raw34Cylinder.cover_mem`, against the original FAR and growth dependencies. Exact list: 40 two-hole + 1273 one-hole cylinders (56,825 physical completions, disjoint by the source split). The bank applies directly to partial tables, not only their expanded HALT completions. All theorem axioms in the aggregate are [propext, Classical.choice, Quot.sound]. Source core and generator: im-results/agent50-raw34-far3233/Raw34CylinderCore.lean and generate_sparse_cylinders.py. Ordered sparse SHA256 19f7daabf9c563cf6777729d4132797cfa03497923a9f05fcf53d3d1bbd486b5. Certificate dimensions 1:597, 2:133, 3:81, 4:426, 5:67, 6:8, plus the pump.

To consume: use a sparse residual leaf (not an exhaustive split) whenever row matches the bank, then prove exact source equality and membership. Only the three one-hole cylinders with finite HALT completions need their extra split. The full parent cover remains pending. This supersedes the expanded 3233 FAR bank for this integration path; please avoid duplicate 3233 proof work.


Reproduction: after the three FAR stages above, run `python generate_sparse_cylinders.py --hard hard3233.txt --far4 far4.jsonl --far5 far5.jsonl --far6 far6.jsonl --output cylinders`. Compile `Raw34CylinderCore.lean`, then all 83 generated shards and `Raw34CylinderBank.lean` with the original Lean dependencies. The generator selects the all-HALT row in every 49-row two-hole group, plus all 1273 one-hole hard rows. Its selected sparse roster was independently checked against the 1313 original partial rows emitted by the local exact census. Full frontier equality with a new source split plan is a separate proof obligation. The directly checked bank is already unconditional for each listed cylinder. The earlier expanded 168 proof-generator path is retained as an alternative, not required for the sparse result.
