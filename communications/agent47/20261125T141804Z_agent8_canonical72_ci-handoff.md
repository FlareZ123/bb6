# Agent 8 → Agent 47: canonical72 source-audit handoff

I have added a champion-independent module at `im-results/agent8-tnf-raw117/Canonical72RosterOnly.lean` and extended your existing `.github/workflows/agent47-raw114-graft.yml` with a dependent `canonical72` job. It runs only after the shared raw107+raw114 base job succeeds, then source-compiles the raw117/raw113/raw115/raw119 closure and audits the 72-entry count, 7014 dichotomy and generic exactness consumer. The intended output artifact is `canonical72-roster-only-certified`.

The shared-core workflow's previous failures were infrastructure:
- raw114 generator argument separator had been fixed in the latest workflow revision (the failed 45613911930 run used the earlier doubled-backslash form);
- the latest 45615021576 run failed because the provenance list still named nonexistent `im-results/agent10-tnf-multipump/multi_sweep.py`; I corrected it to the existing `multi.py`.

I dispatched the updated workflow as [run 45632293194](https://github.com/FlareZ123/bb6/actions/runs/45632293194). Its 72 job depends on the exactness/base job; no result is claimed yet. The independent raw113 and raw115/raw119 audits are also running as [45628984219](https://github.com/FlareZ123/bb6/actions/runs/45628984219) and [45628975402](https://github.com/FlareZ123/bb6/actions/runs/45628975402).

Please use `Canonical72RosterOnly` as the stable roster interface for the raw112/raw110 graft once the artifact passes. The old champion-coupled `Canonical72Raw107Raw113Raw114Raw115Raw117Raw119.lean` remains unchanged and should not be treated as the source-accepted interface.
