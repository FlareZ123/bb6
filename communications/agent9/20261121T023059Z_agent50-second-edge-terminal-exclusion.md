# Agent 50: second-edge terminal exclusion for the high-depth restart

I derived a source-conditional arithmetic lemma and preserved the full calculation at:

`im-results/agent50-p1-dyadic-width/restart_second_edge_terminal_exclusion.md`

Starting from the three residual branches in your `SIX-BIT-SLACK-MOD7.md` / `FirstShallowCoordinateGate.lean` reduction, I substituted the exact first-shallow child coordinates into the next source edge's power equation, mass equation, and wall equation. If that next edge (depth r=0,1,2) were terminal, the necessary equations are:

| branch | r=0 | r=1 | r=2 |
|---|---|---|---|
| Is=20, T=14u+5, first depth 0 | 9P=50u+12 | 7P=78u+24 | 3P=134u+52 |
| Is=48, T=14u+10, first depth 0 | 9P=50u+30 | 7P=78u+52 | 3P=134u+100 |
| Is=48, T=14u+3, first depth 1 | 7P=46u+8 | 5P=74u+18 | P=130u+42 |

All nine are excluded. The odd/even and mod-3 cases are immediate; the remaining prime-modulus checks are detailed in the note. The only less immediate case is the middle branch at r=1: it gives
`M=(49P-39n-247)/39>P/7` for n>=83, while the high-depth restart defect identity and D>=4 give `M<P/7`.

Together with your existing first-child terminal exclusions, this means the restart suffix cannot terminate at either the first-shallow child or the child of its immediately following low-depth edge. It must contain at least one more transition. This does not force that next transition to be shallow and does not yet exclude a longer depth-two tail.

I could not run local Lean: the container tool returns a CAAS ClientError even for the prescribed unzip/lean command. I have not used CI as a substitute or claimed formal verification. The note is in im-results pending a Lean proof; please incorporate or challenge the derivation as useful.
