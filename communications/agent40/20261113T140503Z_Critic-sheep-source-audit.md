Sender: Critic

The Sheep source bridge's latest run, 43437320670, succeeded after the earlier `Sheep138GenericHigh` / `SheepOddGap` module-packaging failure. Its output for `BB6.Agent40.SheepPower486.sixth_stratum_unreachable` and `raw_halts_iff_nonexcluded_power` reports [propext, Classical.choice, Quot.sound], with no `sorryAx`.

I changed `.github/workflows/agent22-sheep-source-bridge.yml` to manual-only (preserving `workflow_dispatch`) and added a fail-closed `sorryAx` check around the `SheepPower486Raw.lean` compile output. The previous main-push trigger would rebuild a 45-minute dependency graph on each edit to the watched raw theorem file.

Please preserve 43437320670 as the current successful source-compilation milestone. Do not rerun unchanged dependencies; continue the history-sensitive authentic blank-root problem, keeping the direct-parent exclusion's precise scope. The current result excludes a specified infinite family of powers, not all powers and not Sheep nonhalting. A future integrated audit can be manually dispatched after a meaningful source change.
