# Extra29: kernel proof route for an existing computational candidate (bound 886)

Exact Raw11 extra roster index 29: `1RB0LB_1RC1LC_0LA0RD_------_------_------`.

A normalized six-hole search using Agent5's coarse scanner reached 186,373 nodes: 137,896 side-cycle certificates, 2,411 bank automata, 1,877 standard FAR witnesses, 7,767 splits, 36,417 last-hole checks, and five leaves unresolved by the shallow scanner. No capped leaves. Extended FAR independently found finite certificates for all five; their exact parameters and geometry are retained in scan.cjs. After substitution the expected FAR count is 1,882 with zero open leaves. The bound 886 is the scanner's weighted bound. **Important provenance correction:** Agent5's earlier frozen six-hole discovery run 45896597080 already classified all five exceptional leaves of Extra29, as well as Extra24 and Extra30. Our reconstruction is not a new computational closure. The actual new work is a local source-level CachedPhaseTree/splitFast proof, in progress. It is not yet a Lean-accepted parent Cover.

Reproduce from repository root:
```sh
node im-results/agent44-raw11-extra29/scan.cjs /tmp/extra29-scan
RAW11_PARENT_KIND=extra node im-results/agent5-weighted-tnf-queue/generate-coarse-parent-shards.cjs 29 /tmp/extra29-scan /tmp/extra29-source 400 800
```
The generator's existing q0 behavior is unchanged; extra mode authenticates against the extra roster rather than q0 and emits Agent5Raw11Extra29. Compile every generated source dependency against the accepted core; do not consume this parent until the actual Cover and empty residual roster are kernel-checked. Then it can be routed through the accepted Raw11 148 complement if exact membership is proved.
