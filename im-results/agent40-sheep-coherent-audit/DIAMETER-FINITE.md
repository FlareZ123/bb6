# Historical finite-diameter census, now explained by a universal theorem

**Current status (6 November 2026):** The former conjecture in this note is now **proved for all dyadic precisions** in [DYADIC-DIAMETER.md](DYADIC-DIAMETER.md). The exact generic quotient diameter is floor(p/2) for every p>=1. The same note establishes that the **freely chosen, single-real-orbit** coherent generic dyadic diameter is also floor(p/2), improving the earlier general coherent upper bound by one return in the pure-dyadic case. Neither theorem classifies the genuine blank-origin Sheep machine.

## Original independent finite evidence

The pre-theorem program [diameter_explore.py](diameter_explore.py) enumerates the complete generic dyadic inverse graph through p=11 and computes every ordered-pair shortest distance. It uses Agent 22's exact complete modular inverse map, not a bounded Turing machine run, and it includes the universal zero-hub edges. Its observed diameters were:

| p | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| diameter | 0 | 1 | 1 | 2 | 2 | 3 | 3 | 4 | 4 | 5 | 5 |

Exact eccentricity distributions: p=10 has {1:18,2:168,3:252,4:72,5:2}; p=11 has {1:20,2:240,3:504,4:240,5:20}. The prior note identified the formula floor(p/2) only as a conjecture because finite enumerations cannot prove it for all p.

## Complete answer and provenance

The new proof shows that canonical inverse words of maximum length k=floor(p/2) consume at least p-1 binary digits. Their associated inverse-map composition therefore forgets **every even terminal target**, permitting a k-edge route to any desired residue. Shorter canonical words route to zero and use the known outgoing-zero hub within k edges. The existing shortest-to-zero theorem supplies the sharp lower bound.

The [Lean 4.36.0-rc2 affine saturation kernel](AffineSaturation.lean) checks the new algebraic core with no sorryAx. [diameter_certificate.py](diameter_certificate.py) checks all maximal-code source/target pairs through p=15; [coherent_diameter_certificate.py](coherent_diameter_certificate.py) checks genuine consecutive return trajectories through p=15 (maximal shell), plus p=9 (shorter shells). The previous all-pairs BFS is independent evidence.

All proofs and computations concern legal *generic synthetic* residue paths or arbitrarily chosen coherent positive starting integers. The machine-source original blank entry is fixed at even section 10, and its fate remains unknown; no complete BB(6) solution follows. External novelty has not been established.
