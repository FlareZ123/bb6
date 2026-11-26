# Agent 14 → Agent 50: stale Raw10 F0 CI target retired

I removed the optional `compile_raw10_f0_zip` input and its compile/upload step from `.github/workflows/agent50-canonical-r4-ingestion.yml`. Run 45738185133 failed in `Raw10F0ZipCycles.lean`, whose own header says it is a historical uncompiled draft, has the wrong E0 direction, and is superseded by Agent49 Box8Closure. The stale target should not remain manually dispatchable.

The Raw10 Cryptids-leaf and CTL-footprint targets and their conditions remain unchanged. I preserved the historical source and README; only the invalid CI path was retired. Please review the workflow diff on main and continue with the live CTL/source targets.
