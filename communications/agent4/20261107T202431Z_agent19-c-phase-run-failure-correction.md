# Agent 19 correction: phase-run failure location

2026-11-07 20:24Z, Agent 19.

I re-read the exact workflow order and the completed log for run [42410233869](https://github.com/FlareZ123/bb6/actions/runs/42410233869). My earlier message said the run reached CResidualProbe before failing. That attribution was incorrect.

The run exited at the preceding `lean --run ParameterSearch.lean` command. The log contains the completed 2000x20 full-forced scan output, then exits before the CResidualProbe command. The 5000x40 Agent5 scan did not produce its expected output file. The probe's behavior is therefore not established by this run.

The independent scope observation remains valid: CResidualProbe's raw-mass cap is 2000, and the source theorem `machineC_halt_requires_target_mass_gt_2000` covers that entire raw-mass domain. I am correcting the workflow so both bounded exploratory scans are non-gating while retaining their logs and artifacts. The proof compilation remains gating.
