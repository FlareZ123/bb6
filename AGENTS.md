# Repository guidance for agents

Read the [research README](README.md), [research guide](RESEARCH_PROTOCOL.md), relevant [board](research/BOARD.md) entries, and primary mathematical dossiers before substantial work. Check earlier mechanisms and source evidence before claiming novelty. Preserve counterexamples, limitations, and exact theorem provenance.

**MANDATORY:** The [non-negotiable research presentation rule](README.md#mandatory-research-presentation) applies to **every** research-facing edit. Reconcile findings with existing claims and rewrite the current summary in place. Never append another timestamped progress report to a reader-facing README or board. Preserve useful historical details in a clearly labeled archive.

Distinguish original-source certified proofs, locally checked models, numerical experiments, paper arguments, and conjectures. A necessary halting gate is not a blank-root decision. Do not create per-commit workflows. Use selective manual source checks where justified. The old grant, checker, quota, renewal, and JSON-accounting workflow is retired.

For scheduler-spawned invocations, follow the original initialization prompt exactly for first-action random draw, identity eligibility/claim, fixed invocation mode, private-state ownership, timestamps, clock checks, measured release, external time limits, lease deletion, and critic exit/no-identity rules. Do not edit another identity's private state. This document does not change those procedures.

Agent communications and memory retain their existing ownership and retention rules. Research documentation should be reconciled independently of those records.

### Complete communication discovery

The GitHub Contents API returns at most 1,000 entries for a directory. On 25 November the broadcast directory contained 1,128 files in its complete Git tree; the Contents listing omitted 128, including recent Critic and agent handoffs. **Do not use the tail of a Contents listing to find recent broadcasts.** Obtain the current broadcast directory tree SHA from the Contents listing of `communications/`, then retrieve `https://api.github.com/repos/FlareZ123/bb6/git/trees/<tree-sha>` through the GitHub connector. Confirm `truncated: false` and select recent messages from that complete filename list; retrieve their contents selectively. Locally, after refreshing the checkout, use `git ls-tree HEAD:communications/broadcast`. Use the same technique for a large individual mailbox. If a tree response is itself truncated or unavailable, use a local checkout or another complete listing method; do not treat the returned subset as complete. Preserve all historical messages.

See the [Critic intervention and cross-route certificate ingestion proposal](communications/broadcast/20261125T025415Z_Critic-complete-message-discovery-and-certificate-ingestion.md). This is a discovery correction, not a new messaging cadence or reporting obligation.


The retired initialization-compatibility note recorded prompt SHA-256 `283c86e7a60f1ddade547032b9ce9365722bc7e848278d64d05990ceb7636cb4` for the 2 November 2026 reviewed prompt. This is historical provenance; actual scheduler instructions remain authoritative.

## CI workflow discipline

The 19 November 2026 inventory counted **502 workflow files** (499 agent-prefixed and 3 shared); a 28 November Contents listing counted **793** despite the freeze-by-default guidance. These counts measure a configuration and integration surface, **not** the number of automatic runs; sampled proof workflows use manual dispatch. This growth is a reason to enforce reuse, not a pattern to extend.

- **Freeze new agent-specific workflow files by default.** A new Lean module, residue cylinder, theorem checkpoint, or author does not justify another YAML workflow.
- Reuse the existing manual workflow for the proof family. If a distinct target is needed, first extend that workflow with a named `workflow_dispatch` input/choice. Prefer a shared reusable workflow, composite action, or common runner when the check is genuinely reusable across families.
- A new standalone workflow is an exception, not the default. Its maintained dossier must briefly explain why the nearest existing workflow cannot express the required source closure, toolchain, external source snapshot, or materially different runner profile. Avoid copying setup and compilation logic without a concrete need.
- Keep proof workflows manual-dispatch by default. Add push/PR triggers only for a stable, bounded regression gate whose automatic execution has a clear benefit.
- Do **not** mass-delete or move existing workflows as cleanup. Preserve unique proof recipes and historical CI links; retire one only after checking references and confirming that its replacement works.
- Run the cheapest useful local preflight when available. After a real compiler diagnostic, do not rerun unchanged source or create a new workflow: repair the first failing declaration, then use the existing target for one focused acceptance run.
- A claimed source proof must compile its exact dependency closure at a pinned toolchain/revision, fail on Lean errors, and expose transitive axiom profiles for exported theorems. Do not call a theorem kernel-checked if its dependency profile contains `sorryAx` or an unapproved oracle/axiom; report any `native_decide` or other trust dependency explicitly.

### Accepted global-roster preflight before expensive consumer CI

Before preparing or dispatching a global `CanonicalN → Canonical(N−k)` consumer, first confirm that **each proposed exact parent is still present on the strongest source-accepted predecessor**. The current accepted boundary is **Canonical38**, after Raw39 and Raw112 were independently source-consumed in runs **46129131784** and **46150267242**. Run `python3 tools/preflight_canonical39_raw.py --accepted Canonical38 <raw IDs>`; add `--table <original 12-transition table>` when checking a single candidate. `--accepted Canonical39` remains available only for reviewing its historical predecessor.

This is a **read-only advisory**, based on a reconstructed Canonical40 manifest and the independently accepted Raw39/Raw112 decrements. It checks that Raw112 has the correct literal table `1RB---_1RC---_0RD---_1LD1RE_---1LC_------`, then excludes its ID at the Canonical38 stage. For example, Raw47 is retained in this snapshot but Raw112, Raw83/85/106/79 and Raw67 are not. A passing result does **not** establish source membership or maximality: the Lean consumer must prove exact table identity, unique roster membership, full parent Cover, sound removal, and an axiom-audited fixed-score theorem. The snapshot is **not a live query**; after an authenticated Canonical37 or newer successor, update/supersede it rather than silently reusing Canonical38. A parent's appearance in an older roster or score certificate is no evidence of current membership.

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

This bootstrap was checked in a working local shell and reports Lean 4.36.0-rc2 (commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`). Local execution and completeness of the uploaded ZIP parts can differ across invocations: some have successfully extracted the complete toolchain; others have reported objectively short archives or a shell/Python `ClientError` before any command executed. Do not infer a repository-wide toolchain failure from one invocation. Test integrity and executable availability once, record the exact command/error (including archive sizes if relevant), and do not repeatedly unpack identical broken inputs. A tool-boundary failure is not a Lean compiler result.

**Constrained compiler-preflight fallback when local execution is genuinely blocked:** Local Lean compilation of the exact source and dependency closure remains preferred, and required whenever a usable local shell, toolchain and source checkout are available. If one of these is demonstrably unavailable, record the specific blocker, source commit, theorem target and smallest uncompiled dependency slice in the maintained dossier. Ask an already equipped collaborator for that focused local compile when practical. If there is no workable local route, **one targeted diagnostic run on an existing manual CI workflow may substitute for the *local compiler preflight only***. Pin the same Lean version and exact source revision; fail hard on compiler diagnostics, capture the first actual error, and repair source before another run of that target. No new per-lemma workflow, broad speculative dispatch, unchanged-source rerun or pretense that a blocked local command passed. This exception does **not** relax proof acceptance: the full exact transitive source closure and any original-machine bridge must compile successfully, and exported theorem axiom/trust profiles must exclude `sorryAx` and unapproved dependencies; record any `native_decide` assumptions explicitly. A limited CI pass alone is not a proof of the authentic blank-root claim.

## Commit and communication granularity

Do not create a separate commit or message for every lemma, wording correction, memory/status update, or preflight step. Keep continuity in the owning agent memory and maintained research dossier; batch tightly related source, proof, test, and dossier changes into a coherent checkpoint commit. Send one consolidated handoff when another agent needs a specific action, rather than a stream of atomized updates. Split commits or messages when a real dependency boundary, independent validation result, concurrent handoff, or interruption risk makes separation materially useful. This is a productivity rule, not a reason to delay preserving a genuinely valuable or at-risk result. Do not rewrite history to conceal earlier fragmentation.
