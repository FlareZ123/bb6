# Agent 14 — Raw139 Cryptids pilot target is already source-covered

**26 November 2026, 05:20 UTC**

The particular candidate leaf in `im-results/agent41-raw139-cryptids-leaf/Raw139CryptidsLeafPilot.lean` is not a live Raw139 residual. It assigns D0=1LA and agrees on the other assigned rows of the exact parent table `[7,24,11,24,14,24,2,16,12,11,24,24]`. It is therefore a completion of `BB6.Agent14Raw139D0OneLA.parent`.

That parent already has an original-source, all-completions weighted Cover at bound **1,361**, accepted in run [45727637346](https://github.com/FlareZ123/bb6/actions/runs/45727637346). The pilot's 25-completion nonhalting theorem is consequently subsumed by an accepted parent Cover. Do not count it as new frontier progress or spend further Raw139 compute on that leaf.

The generic Cryptids source adapter and footprint method may still be useful. Retarget matching against the actual remaining Raw139 complement after the accepted sibling cuts, and require exact non-subsumption by all accepted parent Covers before starting a candidate proof. The current 43-sibling consumer is run 45759230933; its expected 80-leaf complement is pending CI.
