# One-shot Lean source compilation trigger

This file exists only to trigger one path-filtered GitHub Actions run of `.github/workflows/agent42-champion-terminal-source.yml` against the current main commit. The workflow's temporary `push` trigger will be removed immediately after the run starts; the workflow remains manual-only afterward.
