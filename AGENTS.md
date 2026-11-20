# Repository guidance for agents

Read the [research README](README.md), [research guide](RESEARCH_PROTOCOL.md), relevant [board](research/BOARD.md) entries, and primary mathematical dossiers before substantial work. Check earlier mechanisms and source evidence before claiming novelty. Preserve counterexamples, limitations, and exact theorem provenance.

**MANDATORY:** The [non-negotiable research presentation rule](README.md#mandatory-research-presentation) applies to **every** research-facing edit. Reconcile findings with existing claims and rewrite the current summary in place. Never append another timestamped progress report to a reader-facing README or board. Preserve useful historical details in a clearly labeled archive.

Distinguish original-source certified proofs, locally checked models, numerical experiments, paper arguments, and conjectures. A necessary halting gate is not a blank-root decision. Do not create per-commit workflows. Use selective manual source checks where justified. The old grant, checker, quota, renewal, and JSON-accounting workflow is retired.

For scheduler-spawned invocations, follow the original initialization prompt exactly for first-action random draw, identity eligibility/claim, fixed invocation mode, private-state ownership, timestamps, clock checks, measured release, external time limits, lease deletion, and critic exit/no-identity rules. Do not edit another identity's private state. This document does not change those procedures.

Agent communications and memory retain their existing ownership and retention rules. Research documentation should be reconciled independently of those records.

The retired initialization-compatibility note recorded prompt SHA-256 `283c86e7a60f1ddade547032b9ce9365722bc7e848278d64d05990ceb7636cb4` for the 2 November 2026 reviewed prompt. This is historical provenance; actual scheduler instructions remain authoritative.

## CI workflow discipline

At the 19 November 2026 inventory, `.github/workflows/` contained **502 workflow files: 499 agent-prefixed and 3 shared**. The sampled current proof workflows were manual-dispatch workflows, so this is not a claim that all 502 execute automatically. It is an accumulated configuration and maintenance surface, not a pattern to extend.

- **Freeze new agent-specific workflow files by default.** A new Lean module, residue cylinder, theorem checkpoint, or author does not justify another YAML workflow.
- Reuse the existing manual workflow for the proof family. If a distinct target is needed, first extend that workflow with a named `workflow_dispatch` input/choice. Prefer a shared reusable workflow, composite action, or common runner when the check is genuinely reusable across families.
- A new standalone workflow is an exception, not the default. Its maintained dossier must briefly explain why the nearest existing workflow cannot express the required source closure, toolchain, external source snapshot, or materially different runner profile. Avoid copying setup and compilation logic without a concrete need.
- Keep proof workflows manual-dispatch by default. Add push/PR triggers only for a stable, bounded regression gate whose automatic execution has a clear benefit.
- Do **not** mass-delete or move existing workflows as cleanup. Preserve unique proof recipes and historical CI links; retire one only after checking references and confirming that its replacement works.
- Run the cheapest useful local preflight when available. After a real compiler diagnostic, do not rerun unchanged source or create a new workflow: repair the first failing declaration, then use the existing target for one focused acceptance run.
- A claimed source proof must compile its exact dependency closure at a pinned toolchain/revision, fail on Lean errors, and expose transitive axiom profiles for exported theorems. Do not call a theorem kernel-checked if its dependency profile contains `sorryAx` or an unapproved oracle/axiom; report any `native_decide` or other trust dependency explicitly.

## Local Lean 4.36.0-rc2 bootstrap

The supplied split files concatenate to an outer ZIP whose member is `lean-4.36.0-rc2-linux.tar.zst`. Extracting the ZIP alone does **not** install Lean; extract the inner Zstandard tar archive as well:

```bash
mkdir -p /tmp/lean
cat /mnt/data/lean-4.36.0-rc2-linux.zip.{001,002} > /tmp/lean.zip
unzip -q /tmp/lean.zip -d /tmp/lean
tar --zstd -xf /tmp/lean/lean-4.36.0-rc2-linux.tar.zst -C /tmp/lean
export PATH="/tmp/lean/lean-4.36.0-rc2-linux/bin:$PATH"
lean --version
```

This bootstrap was checked in a working local shell and reports Lean 4.36.0-rc2 (commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`). A separate shell/Python tool-boundary error that prevents even trivial commands from executing is an environment blocker; the extraction steps cannot repair it. Do not use CI as a substitute for the required local preflight.

## Commit and communication granularity

Do not create a separate commit or message for every lemma, wording correction, memory/status update, or preflight step. Keep continuity in the owning agent memory and maintained research dossier; batch tightly related source, proof, test, and dossier changes into a coherent checkpoint commit. Send one consolidated handoff when another agent needs a specific action, rather than a stream of atomized updates. Split commits or messages when a real dependency boundary, independent validation result, concurrent handoff, or interruption risk makes separation materially useful. This is a productivity rule, not a reason to delay preserving a genuinely valuable or at-risk result. Do not rewrite history to conceal earlier fragmentation.
