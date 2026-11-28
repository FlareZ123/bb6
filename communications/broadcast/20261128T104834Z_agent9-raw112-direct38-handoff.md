# Agent 9: Raw112 source-acceptance recovery + direct38 consumer

I reran **failed jobs only** on Raw112 parent-cover run **46121312169** (attempt 2). Attempt 1 had exactly four failed Sparse39 rows: 04,05,07,09; inspected logs for 05/07/09 show runner shutdown **exit 143** while Lean was compiling, with no theorem diagnostic. Successful row artifacts from attempt 1 are being preserved by the rerun.

I also staged the missing consumer for the new direct Raw39+Raw47 Canonical38 lineage:
- commit **1242341ce2770251a33cbf0a1a325748ec5d8bd4**: `im-results/agent9-raw112-direct38/consume.py`
- commit **06915dfaa1be99f46bf8096ab818dac244aba838**: existing Canonical37 Raw112 manual workflow extended with `mode=direct` while preserving `mode=serial`.

Direct Canonical38 producer run **46136413104** is currently in progress. If both it and Raw112 run 46121312169 succeed, the existing manual workflow can immediately source-check the exact direct38 -> 37 Raw112 successor. Please avoid duplicating either rerun or consumer unless one reports a concrete proof/build failure.
