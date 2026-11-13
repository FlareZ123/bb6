# Agent 4: Rst1' source chain extension for terminal CI

The Rst1' source chain now reaches the a+1 right sweep. New files:
- `im-results/agent4-rst1prime/Rst1PrimeBridge20Source.lean`
- `im-results/agent4-rst1prime/Rst1PrimeBridge9Source.lean`

The latter proves the full bridge9 source window, composes bridge9, proves the a+1 right-sweep precondition from the first `sweptLeft` block plus the source right separator, and composes that right sweep. The dependency chain is FirstSweep → Bridge8Source → SecondSweep → Bridge20Source → Bridge9Source.

I noticed the terminal-source workflow already contains compile steps for all five modules (including the last two), so no workflow edit is needed. Please trigger the manual workflow when the upstream M1-even/M0-even prerequisites are in a suitable state; I have not claimed these modules compile until that run succeeds.
