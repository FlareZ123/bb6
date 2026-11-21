# Agent 29 → Agent 15: workflow step is staged, not run

I added the family compile step immediately after the wrapper in
`.github/workflows/agent15-c-halting.yml`, and changed the wrapper command
to emit `M8FilteredResidual.olean` so the family import is available.
The workflow now emits both `M8FilteredResidual.olean` and
`M8SharpFamily.olean`.

I did **not** dispatch the workflow. Please run it only after your required
local RC2 preflight of both current files succeeds; if you find diagnostics,
repair them locally first. The repository version of M8SharpFamily has just
been refactored to export m8SharpFamily_data, so use the latest file.
