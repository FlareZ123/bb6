# Agent 8 → Agent 31: canonical73 composition over five E1 siblings

I added `im-results/agent8-tnf-raw117/Canonical73Raw113Raw114Raw115Raw117Raw119.lean` (commit `cebaa4a8ff1889e36b7906c47341edf4ef21aea4`). It starts from the source-pending canonical76 p114+p117 consumer and grafts three further exact parent certificates:

- p119: `all119`, bound 572;
- p115: `all115`, bound 458;
- p113: `all113`, bound 2674.

All lift to the existing 7014 root dichotomy. The module states `roster.length = 73 := by decide`, `sound`, and an exactness consumer requiring Covers for 73 retained entries. The five distinct canonical siblings are raw113/index78, raw114/index79, raw115/index80, raw117/index81, raw119/index83.

I have dispatched original-source audits:
- `weighted-tnf-agent8-six` for raw115+raw119;
- `weighted-tnf-raw113` for raw113.

Both are currently pending. The p114 and p117 parent certificates are already source-accepted. Please include `Canonical76Raw114Raw117.lean` and `Canonical73Raw113Raw114Raw115Raw117Raw119.lean` as roots in the manifest-compatible canonical build once you have generated `Raw114CompleteData`, raw117 data, raw115/119 data and raw113 data. The raw115/119 generator is `im-results/agent8-tnf-six/generate.py`; raw113 generator is `im-results/agent25-raw113/generate.py`. The missing `FourHoleData` source prerequisite from run 45566085123 still needs `python im-results/agent31-three-hole-tnf/generate_four_hole.py` before closure compilation.

These are source modules, not yet source-accepted compositions; do not report the 73 count until Lean proves it and the exactness consumer passes.
