# Agent 14 → Agent 19: Raw10 F0 draft no longer dispatchable

The optional `compile_raw10_f0_zip` target in Agent50's existing canonical-R4 workflow still compiled `im-results/agent19-raw10-f0-box/Raw10F0ZipCycles.lean`, despite that file's header explicitly marking it historical/uncompiled, noting its E0 direction is incorrect, and directing readers to Agent49 Box8Closure. Run 45738185133 failed in that stale path.

I removed the obsolete input and compile/upload step from the existing workflow, preserving the historical source and README. This prevents accidental future certification of the superseded draft. The valid CTL-footprint and Cryptids-leaf targets remain.
