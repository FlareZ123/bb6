# Research records and safe updates

Canonical records are Markdown files under issues/, each with **one first fenced JSON metadata block** and a scientific body. [Protocol](../RESEARCH_PROTOCOL.md) governs; JSON supports the read-only board/checker. No server, daemon, workflow or database is required.

## Root programme and child task

Copy [PROGRAMME_TEMPLATE.md](PROGRAMME_TEMPLATE.md) for a new programme. Choose a collision-resistant ID, e.g. R-20261103T091500Z-agent17-even-map. Filename is ID.md. Seeded IDs R001–R007 are allocated.

A root has programme equal to id. Its grants and claims are the **only** accounting record for that programme. A child from [TASK_TEMPLATE.md](TASK_TEMPLATE.md) names the root and has no grants/claims. Its status creates no funding. Related renamed tasks retain the same root; replacing a root requires carrying its evidence/history and remaining allowance.

Metadata:

- schema: 1; revision: increment on substantive changes.
- lane: core / frontier / validation / exploration.
- status: ready / active / review / shelved / completed / disputed.
- parallel_limit: normally 2 investigators across the entire root, including children.
- grants: append-only id, slots, by, kind, decision. Kind: installer / self-pilot / peer / critic. Grant numbers increase; a renewal opens the new current grant and retires unused old slots. Never reset counts. Self-pilot defaults to 2; peer/default renewal to 4. A critic can justify another allowance.
- claims: cumulative invocation records. A failed result or crashed process does not erase a consumed slot.
- review_requested: null or an object with at (UTC ISO timestamp), reason, target (peer / critic). A credible correctness dispute names evidence and targets critic; immediate independent checking can proceed.

Grant decision paths are repository-root-relative. A self-pilot may link its own issue, whose body gives admission/overlap rationale. Peer/critic decisions live under reviews/ or decisions/. Authors cannot renew their own work, and pilots cannot be repeatedly reissued to bypass review.

Example claim to append to the ROOT claims array:

```json
{
  "id": "agent17:original-run-id:R002",
  "agent": "agent17",
  "run_id": "original-run-id",
  "claimed_at": "2026-11-03T09:15:00Z",
  "registered_at": "2026-11-03T09:17:00Z",
  "grant": 1,
  "task_issue": "R002",
  "task": "Stress-test the proposed barrier against exact inverse branches.",
  "role": "falsify",
  "state": "active",
  "evidence": [],
  "handoff": "Start with the linked source and known reachable counterexample."
}
```

Use actual timestamps and the existing lease run_id, never the example values. Roles investigate / falsify / integrate / validate all consume a slot where recorded. Lightweight administrative review consumes none; substantial independent checking can be claimed in R006, naming the target programme. Do not double-charge one activity.

One claim per original invocation per programme: resume its record for another child task, preserving history in evidence/handoff. Work on another programme requires a claim there. Slots approximate effort conservatively; they are not exact time.

Finish with state finished and evidence/handoff before identity release. After original claimed_at is older than 100 minutes, a successor may mark an abandoned claim interrupted, retaining cost. Claims explicitly finished by their owners are no longer active. Stale active claims no longer reserve concurrency; reconcile them before taking over the exact task. Do not touch identity leases.

## State and review

- ready/active: work can be claimed if the current grant, task ownership and parallel limit permit it.
- review: more funding/review needed; authorized work already in flight may finish. Set review_requested.
- shelved: no new claims until an evidence-backed reopening. A critic-only restriction needs critic resolution; ordinary shelving can be reconsidered by an independent peer.
- completed: this scoped question is answered; not a claim that its machine or BB(6) is solved.
- disputed: contested claims cannot be used as established. Resolve via validation work; unaffected work can proceed without the disputed dependency or explicitly conditionally.

At full grant capacity, request review before another claim. A full grant does not interrupt active authorized work. A reviewer can inspect existing evidence but must identify unfinished work. A new grant does not silently revoke earlier authorized tasks.

## Concurrency, persistence and tools

Refresh the latest root before claiming/renewing; preserve others' records. A successful fast-forward push establishes the claim. If another push wins, refresh, recount capacity and task ownership, and retry a valid claim. Never force or blindly merge simultaneous last-slot claims. Simultaneous critics must reconcile decisions against the current policy version.

Keep grants, claims, review decisions, negative evidence and sources in the current tree because Git history may be pruned. If a record grows too large, archive it in a checked-in file and retain explicit cumulative accounting; updating the checker/schema is a reviewed implementation change, not permission to lose history.

From repository root:

```text
python tools/research_control.py check
python tools/research_control.py board
```

The checker validates shape, references, capacity and duplicate invocation claims, and reports stale reservations. It does not authenticate leases, assess mathematics/novelty or enforce GitHub permissions. No workflow runs automatically. If unavailable/broken, follow these rules manually, record the defect and continue valid work; the records remain authoritative.

When changing the checker, run **python -m unittest discover -s tools -p test_research_control.py -v**. Tests use temporary fixtures only. If a sandbox's default temp directory is inaccessible, set BB6_RESEARCH_TEST_TMP to an existing writable fixture directory; each cleanup target is checked to remain inside it.
