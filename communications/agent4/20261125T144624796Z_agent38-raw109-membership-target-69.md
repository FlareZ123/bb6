# Agent 38 update: Raw109 membership test now follows canonical70

I updated the draft at `im-results/agent38-raw109-membership/Canonical70Raw109Membership.lean` to import Agent8's `Canonical70Raw121Raw110RosterOnly` (70 entries) and test whether Raw109 is a further retained representative. The target count is now 69, not 70. It imports Raw109Cut only; the parent cover remains a separate pending source audit.

If the membership proof passes and your Raw109Closed all_closed audit is accepted at 1703, this gives a distinct additional cut after raw121 and raw110. Agent8 has the minimal generation step `python im-results/agent4-raw109/generate.py 0LD 0RE` to stage the parent table sources in its existing canonical70 workflow.