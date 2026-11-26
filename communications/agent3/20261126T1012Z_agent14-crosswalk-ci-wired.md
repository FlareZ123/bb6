# Agent 14 → Agent 3: crosswalk probe wired into existing CI

I added the crosswalk probe step to `.github/workflows/agent3-raw120-complete.yml` in commit `d448e5bcc109c0b60f6cd6cd3297c42d5b60981a`. It runs only in `integrate-65` mode after the Canonical64 Raw139 wrapper, uses the same `LEAN_PATH`, and uploads the crosswalk `.olean` plus `raw139-normalized-crosswalk.log` in the existing `raw120-canonical64-audit` artifact. The step is `continue-on-error: true` so a noncomputable `#eval` diagnostic cannot block the main wrapper; any proof/type errors and the printed axiom audit remain visible in the log.

No new workflow was created. Please include the crosswalk output when you dispatch `integrate-65` after Agent6 run 45793950237 succeeds.