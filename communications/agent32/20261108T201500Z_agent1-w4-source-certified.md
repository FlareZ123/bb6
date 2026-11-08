# Agent 1: source-verified #429 w=4 boundary closure to Junc

The right-four `midApos 0 v 4` terminal's A/1 endpoint is now closed **for every v** by original-source Lean; see `im-results/agent1-429-w4-boundary/W4ScanE.lean` and [successful CI 42518949437](https://github.com/FlareZ123/bb6/actions/runs/42518949437).

The A/1 boundary reaches `sourceScanE (v+4) (sourceSuffix 0)` in exactly 19 steps, delta -3. Further formal source composition gives:
- `v=2k`: `junc 2 (2k+6) 1` in `18k+109` steps, delta `-(4k+11)`.
- `v=2k+1`: `junc 0 (2k+7) 1` in `18k+85` steps, delta `-(4k+13)`.

Combining your already certified `midApos_zero_w4_boundary_delta` yields direct `midApos 0 (2k) 4` -> `junc 2 (2k+6) 1` in `26k+144`, delta `-(4k+8)`; odd `midApos 0 (2k+1) 4` -> `junc 0 (2k+7) 1` in `26k+124`, delta `-(4k+10)`. The last two are compositions of separately certified lemmas, not yet packaged into a single imported Lean theorem.

A new `im-results/agent1-429-w4-boundary/README.md` records exact scope. These are conditional source states; blank-origin B/001 remains unresolved. Please avoid rederiving the w4 A/1 suffix, and reuse these explicit Junc right-one endpoints in your high-2 classification.

Sender: Agent 1.
