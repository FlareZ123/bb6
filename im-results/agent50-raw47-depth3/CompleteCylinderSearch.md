# Raw47 depth-three complete-cylinder search (2026-11-27)

Exact parent: `1RB---_1RC---_0RD---_1LD0RC_------_------`.

## New results and limitations

Use the existing agent7-raw49/cut.cpp to exhaust the 1212 depth-three open cylinders all the way through the final hole, with step cap 1000, lookback 32, depth 7. The depth-three roster SHA-256 is `4ae501c6ae90d482f77d8ba65b060717112e402571f887c20fdcd4c4b0bce41d`. Full search: 1,873,140 translated-cycle leaves, 493,596 last-hole leaves, 46,742 open leaves, 104,939 splits and 120 aliases. All counts are discovery data.

46 complete depth-three subtrees have no remaining open or alias leaves; together they have 29,509 cycle leaves, 4,508 last-hole leaves, 1,477 splits. Maximum first-hole query 221; generated weighted bound 227. Use generate_closed.py for exact table proofs, not the simulation counts as a theorem. At this checkpoint 24 independent generated modules passed local Lean 4.36.0-rc2 against the accepted Raw49 dependency artifact (run 45882523160, artifact 15148276977): IDs 1011,1014,1019,1025,352,355,359,362,437,438,442,356,370,365,417,124,121,396,1185,1080,122,123,131,1048. Each states a weighted bound for every compatible completion, and its quotient-compatible version. Other IDs remain candidates until kernel checked. Full source closure and global roster integration are not yet accepted.

## Reproduce

From repo root:
```sh
mkdir -p /tmp/raw47
g++ -O3 -std=c++20 im-results/agent7-raw49/cut.cpp -o /tmp/raw47/cut
/tmp/raw47/cut '1RB---_1RC---_0RD---_1LD0RC_------_------' 1000 32 3 /tmp/raw47/d3
python im-results/agent50-raw47-depth3/generate_closed.py /tmp/raw47 /tmp/raw47/generated
```
With source-accepted dependency .oleans in LEAN_PATH, compile each generated module with lean -o. Check the printed axiom profiles; no sorryAx or native_decide. Avoid the old invalid FAR6 preloader bank.

## FAR follow-up

For all 167 depth-three parents with 1–5 remaining open descendants after the full cut, there are 441 descendant tables. Existing FAR bank search through 5 states certified 410, leaving 31. This closes 143 parents computationally, including the ten already-known direct FAR5 parents. Combined with the 46 cycle-only parents, 179 additional parents are candidates for removal beyond the ten old direct FAR5 closures. A six-state FAR search timed out locally with no extra certificates before termination. Do not interpret timeout as exhaustive failure. Next step: regenerate and formalize the 133 new complete FAR-augmented subtrees, then close more of the remaining depth-three parents. No exact BB(6) upper bound established.
