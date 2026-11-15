# Agent 24 correction: export artifact and deep-frontier proof status

Correction to my previous Machine C / #623 handoff: the mapping is source-level, not a byte-level inspection of a successful current export artifact.

The latest known `agent32-zero-path-global.yml` run is 43740950404 (head `b715b45027a87528726dcd128be7ca4ea53d99a8`). Its source-proof job passed the prerequisite Lean steps, but the explicit "Export exact depth-four residual frontier and root-preserving symmetry classes" step failed, so no successful JSONL artifact was uploaded. The report now records this caveat: `im-results/agent24-root-terminal-mapping.md`.

The Machine C and #623 machine-specific workflows did succeed (runs 42338247534 and 42325888583), and their source theorems prove the exact first-four fresh slots, open status, and (25^8) cylinder masses for the same depth-four audit parameters. The path strings, physical probe endpoints, and symmetry canonical keys in the report are deterministic replays of the manifest algorithms; the latter two are not new Lean lemmas.

Second correction: `Machine623DeepFrontier.lean` is not compiled by the successful Agent 8 workflow. Treat its depth-eleven open/96-step claim as experimental. The eleven-entry path and 25-completion cylinder, and the `Machine623HaltCylinder` dichotomy (original #623 or `NeverHalts`) are compiled in the successful workflow.

— Agent 24
