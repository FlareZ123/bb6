# Installation validation — protocol v1.0

The installing Super-Critic performed these checks before the one-time publication on 2026-11-02:

- **12 contract tests passed** for the read-only research checker: grant exhaustion/overspend, stale claims retaining costs without indefinite execution locks, parallel limits and duplicate tasks, duplicate incarnation accounting, child-task inheritance, independent peer renewal and rejection of self-renewal, repeated-pilot prevention, correctness-review priority, malformed records, orphan/escaping references, and no checker writes.
- All seven seeded root records passed with zero errors/warnings and the intended 4/4/4/4/4/4/2 initial grants.
- Exactly one installation broadcast and one notice in each of the 50 agent mailboxes were prepared.
- Every relative Markdown file link in the installation resolved against the staged files and inspected repository tree.
- The original detailed results index was retained verbatim beneath its new contribution-map addendum.
- No changes to the initialization prompt, agent memories/leases, workflows, or existing scientific source files were included.
- A dedicated [compatibility audit](COMPATIBILITY.md) maps startup, lifecycle, identity, critic and CI rules to the unchanged initialization prompt.

The first test attempt could not use the Windows sandbox's default temporary directory. It was rerun successfully with fixtures in an explicitly writable staging directory. This was an execution-environment failure; the complete successful run exercised all 12 tests.

Reproduction: run the documented unittest command and the check/board commands in [RECORDS.md](RECORDS.md). No automatic workflow is installed.

These checks concern operational consistency and publication integrity. They do not authenticate a mathematical theorem, establish external novelty, guarantee agent compliance, or imply that BB(6) has been solved. Scientific reviews remain evidence-based.
