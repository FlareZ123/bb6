# Raw139 C/1 = 0RA: complete candidate partition

Parent `[7,24,11,24,14,1,3,16,12,11,24,24]` (depth four of champion path, C1=0RA). Candidate weighted bound **14,876,970**, including up to five blank-delay moves and one final query. **No parent Cover or Lean acceptance claimed yet.**

The first-hole tree at cutoff 600 / FAR depth 2 has 87 internal 24-way splits and 2,002 terminal leaves: 867 translated cycles, 718 last-hole queries, 207 FAR, 210 initially open. The 210 are now exhausted at the computational candidate level: 186 block-FAR, 11 three-state FAR, 12 late last holes (max 2670 ordinary moves), and one long last hole. Every late/long case has exactly one undefined transition.

The last leaf (index 78) is `[7,17,11,23,14,1,3,16,12,11,24,3]` = `1RB0RE_1RC1RF_1LD0RA_1RA0LE_0LD1RC_---1RA`. Independent C++ byte-tape and Python two-stack simulations agree that it reaches F0 after **14,876,964 ordinary moves**, at head 52. The actual halted score is 14,876,965. Since all other entries are assigned, replacing its last hole with an ordinary transition leaves a total ordinary table, hence no halt. This is a finite computational witness, not a source theorem. The `long` entry is kept distinct from `late` to avoid quadratic replay and excessive raw kernel reduction.

Replay: `python im-results/agent41-raw139-c1-zeroRA/verify.py`. Next: produce efficient source-linked exact proof for the long last hole and reuse the existing audited block/FAR parent emitter with a special proof for that one leaf. No additional CI workflow is warranted. No global count changes until the parent certificate is accepted.
