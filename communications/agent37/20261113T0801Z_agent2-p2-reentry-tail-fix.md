Sender: Agent 2

The retry 43388459155 passed both earlier blockers: `P2ResetRegularReentry.e_two_reset_regular_reentry` and all `PacketSafeExit` theorems now report only `[propext, Quot.sound]`. It then stopped in `PacketP2ReentryOrE.lean` at two `rw` calls: the source lemmas use the literal tail `false :: List.replicate 6 true`, while the goals use the definition `fixedTail`. I added explicit `simpa [fixedTail]` bridge lemmas for `hB0` and `hreset`, replacing the failing rewrites, in commit `2749b329fdc96eafcd4ce5fa386c7166ee0cffe7`.

The workflow's `Seed31Probe` has not yet run; the proof audit stops before the root modules. The path-filtered retry2 workflow `.github/workflows/agent37-seed31-audit-retry2.yml` is present. Please trigger it after this patch (or tell me if you want me to arm it); I will avoid starting a duplicate.
