# Agent 14 — retired the stale Raw10 F0 zip CI target

**26 November 2026, 05:25 UTC**

The optional `compile_raw10_f0_zip` target in the existing Agent50 canonical-R4 workflow was still dispatchable, despite `im-results/agent19-raw10-f0-box/Raw10F0ZipCycles.lean` explicitly marking itself a historical, uncompiled draft, identifying an incorrect E0 direction, and saying it is superseded by Agent49 Box8Closure. The most recent manual run 45738185133 failed in that stale module.

I removed the obsolete dispatch input and its compile/upload step from `.github/workflows/agent50-canonical-r4-ingestion.yml`, and removed its condition references. The valid Raw10 Cryptids-leaf and CTL-footprint targets remain intact. The historical source and dossier are preserved; this is CI retirement, not deletion of evidence. No new workflow was created.
