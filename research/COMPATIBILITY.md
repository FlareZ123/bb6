# Compatibility with the scheduler initialization prompt

The maintainer supplied the agent initialization prompt for review and authorized installation without editing it. Reviewed prompt SHA256: `283c86e7a60f1ddade547032b9ce9365722bc7e848278d64d05990ceb7636cb4` (2026-11-02). The prompt itself is not copied or changed here.

| Prompt requirement | Protocol behavior |
|---|---|
| Actual random draw is first action; mode stays fixed | README and AGENTS explicitly preserve it for future scheduler invocations. The installing Super-Critic was directly appointed by the maintainer, not a new ordinary scheduler run. |
| Normal identity must be correctly claimed first | Programme task claims occur after the existing identity claim; they neither create identities nor replace eligibility checks. |
| Original claimed_at; no refresh; 100-minute eligibility | Programme claims reference that original run and use its 100-minute stale-safety threshold; no identity lease is edited by critics. |
| Clock checks after checkpoints; 70-minute release; 90-minute external cap | All preserved. Programme grant exhaustion is a work-selection event, never a new exit condition. |
| Checkpoint does not require messages/new planning | Protocol reads happen at startup or substantial task/renewal boundaries. Productive work continues across checkpoints. |
| Final lease deletion is last mutation | Issue handoff and own-memory updates happen before the existing release sequence. |
| Critic has no identity or memory/lease authority | Explicit in root instructions and critic checklist. Decisions are shared files; no critic execution lease is introduced. |
| Governance/methods intentionally unspecified; agents may create mechanisms | This maintainer-authorized convention fills that permitted space. Local autonomy remains inside funded questions and the protected pilot route. |
| Critics' mathematical recommendations are not facts | Administrative priority does not confer truth. Agents can challenge conjectures, errors and novelty claims with evidence. |
| Persistent memory; external termination; history pruning | Issue records contain handoff and cumulative history in the current tree. A replacement incarnation inherits scientific costs rather than resetting them. |
| Communication through new broadcast/mailbox files | One immutable installation broadcast plus a notice in each of 50 mailboxes; no other messages or private files are changed. |
| Valuable intermediate/negative research; no deliverable per checkpoint | Long proofs can span renewed grants; negative evidence and bounded speculation count. No mandatory theorem per invocation. |
| No per-commit workflows; existing retry/log rules | No workflow is installed/changed; checker runs manually. CI diagnostics retain the instructed targeted Actions tool and network retry rules. |

A future materially changed initialization prompt should be compared with this table. Preserve higher-priority runtime instructions; report exact conflicts and continue unaffected work. The board is not a scheduler, timekeeper, identity allocator or replacement prompt.

## Failure scenarios explicitly covered

- Critic unavailable: independent peer renewal, other funded work or a bounded new pilot; no waiting/early exit.
- Owner killed: consumed slot/evidence retained; stale task reservation expires under original timestamp safety rule.
- Concurrent last-slot claims: refresh/recount after non-fast-forward rejection; no blind merge or force.
- All familiar directions stagnant: protected new-method pilots, frontier work and evidence-backed reopenings remain available.
- Checker unavailable or wrong: manual documented semantics, bounded debug task, no global block.
- Critic makes an incorrect scientific claim: preserve challenge/counterexample; administrative rank cannot settle it.
- New result supersedes an old instruction: refresh sources and record the superseded decision rather than repeating the completed task.
- Governance causes overhead: successor critics can simplify with versioned rationale and a reconsideration condition.
