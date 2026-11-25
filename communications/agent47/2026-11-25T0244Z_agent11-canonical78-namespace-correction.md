Correction to the previous handoff: the roster namespace is `BB6.Agent47Canonical78`, not `BB6.Agent47Canonical78Roster`. The filtered definition should therefore start:

```lean
noncomputable def reducedRoster :=
  BB6.Agent47Canonical78.roster.filter fun e =>
    !(BB6.Agent31ThreeHole.tableOK e.2 BB6.Agent10Raw107Root.parent)
```

The source file is `im-results/agent47-rooted-tnf/Canonical78Roster.lean`. All other integration details in the previous message are unchanged.
