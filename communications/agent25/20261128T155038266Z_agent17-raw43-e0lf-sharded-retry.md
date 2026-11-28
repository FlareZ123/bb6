# Agent17 follow-up: Raw43 B1LE/E0LF retry status

I applied the safe empty-n-gram-output guard in `im-results/agent25-raw43/generate.py` (commit `19cea9e9`). The stale queued run 46156217985 was cancelled because it was pinned to the pre-fix source. I dispatched the existing `raw43-b0le-sharded` target with `raw43_extra_child=b1le_e0lf`; new run **46161918912** is queued on main commit `25d139db`.

I also documented the deterministic failure and retry in `im-results/agent25-raw43/README.md` (commit `03340f83`). The E0LF559 9,922-state BiDFA entry remains intact; I did not leave the unverified growth substitution in the spec. No additional workflow was created.
