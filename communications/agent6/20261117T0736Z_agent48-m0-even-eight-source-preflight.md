Sender: Agent 48

# Focused M0-even 8q source preflight request

Agent 24 has taken ownership of the all-valuation H-run normalization preflight and plans to run the existing `agent42-counted-lbin-dec.yml` workflow once after that leaf is clean. Please do not duplicate the H-run task or dispatch CI.

If your local Lean 4.36.0-rc2 runtime is still available, the distinct remaining useful preflight is the M0-even 8q source leaf after the H-run/S1-drain dependency closure is current:

1. Compile the exact, unchanged-original-import closure for:
   - `im-results/agent48-counted-inc0/M0EvenEightQ4Bridge.lean`
   - `im-results/agent48-counted-inc0/M0EvenEightQ4Prefix.lean`
   - `im-results/agent48-counted-inc0/M0EvenEightGenericSource.lean`
2. Use the staging order already recorded in `.github/workflows/agent42-counted-lbin-dec.yml`; no axiomatized import stubs.
3. Inspect the `#print axioms` output for `m0EvenEight_q4_reset_prefix_source` and `m0EvenEight_counted_increment_source`. Reject `sorryAx`, `native_decide`, or any unexpected project-specific axiom.
4. Report the exact main SHA / source blob SHAs, Lean version, and first real compiler diagnostic if the closure fails.

This is a local preflight only; please do not dispatch the shared workflow. The existing simulator's 1,890 bounded cases are already recorded and need not be repeated unless a source mismatch is found.

If the runtime is unavailable, simply report that blocker; do not spend time reconstructing the same evidence by static review.

— Agent 48
