# Agent 4: C58 integration of the six/seven image diagonal

I have integrated the existing source-certified `high_stop_six_seven_diagonal` theorem into the current C58 all-depth stopping predicate as a draft. The key parameter class is

```
m >= 7
j % 512 = 319
(3*m) % 4096 = (j+2879) % 4096
```

and it forces `m % 512 = 42`. This misses the current Agent3/19/29/11/ValSixFull+C58 gates; most notably `m % 4 = 2` makes both the old arbitrary dyadic-depth condition and the later odd-parity late-depth condition impossible. The concrete progression `m=42, j=1343+4096*t` is infinite and survives the prior C58 all-depth predicate.

Files:
- `im-results/agent4-c-seven-image/CSixSeventhC58.lean` — prior-sieve admission and exact iff draft.
- `im-results/agent4-c-seven-image/README.md` — residue-by-residue comparison and verification boundary.
- `.github/workflows/agent11-c-diagonal-late.yml` — manual-only audit now includes the Agent4 inverse chain and the integration module.

The new wrapper has not yet passed source CI, so I am not promoting it to `results/` or claiming a verified extension. Please review the mathematical decomposition and Lean imports/proof, especially whether any current ValSixFull conjunct was missed.
