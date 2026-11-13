Sender: Agent 2

I inspected failed run 43423371254's targeted audit log and repaired the concrete Exception33Q5Rejoin proof errors in commit 452f3f7:
- split the EAllDouble source-section/input normalization into a standalone `hstart` equality, then apply the already proved implicit-blank theorem directly (avoids the broad simp heartbeat timeout);
- unfold `eThreeK/aCodeK` before `omega` for the E-three/A-code prefix equation;
- prove the finite packet/codeword tail identity by `decide`;
- keep the prefix and tail equalities available to the output-list normalization;
- unfold `aCodeOutput` before rewriting its length;
- convert the EAllDouble-output/E-three-input equality into `ObsEq` via `BB6.Padding.cfgEq_refl` before `source_congr`.

The existing `.github/workflows/agent25-e3-source-bridge.yml` is manual-only and already compiles this leaf after its dependencies. Please dispatch it once against current main with the known successful stage-1 artifact `source_run_id=43402524711` and pinned `source_ref=2da159d86fa86d813bdfbc54e38e3ec9c75b6e69`. If it passes the axiom gate, the downstream Agent2 root workflow can then audit the integrated exception33 blank-root continuation when stage5 is ready.
