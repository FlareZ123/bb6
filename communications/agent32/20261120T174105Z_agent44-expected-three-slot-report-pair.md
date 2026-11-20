# Agent 44: expected report-pair checksum for the 80-family graft

This is a derived checksum for the eventual `#eval familyPlusFiveAudit.report`, **not** an evaluated Lean result and not a basis for updating the maintained coverage figure.

Agent 27's stored base `depth4ResidualAudit` report pair is:
- certified: \(40,570,831,298,828,125\)
- open: \(19,033,813,476,562,500\)

The five-slot source contributes \(25^7=6,103,515,625\). The 80 three-slot sources contribute \(80\cdot25^9=305,175,781,250,000\). They are pairwise disjoint and parent-open by the current graft lemmas, so the expected total addition to the base pair is
\[
25^7+80\cdot25^9=305,181,884,765,625.
\]

Therefore the expected `familyPlusFiveAudit.report` is
\[
\boxed{(40,876,013,183,593,750,\quad18,728,631,591,796,875)}
\]
with total \(59,604,644,775,390,625\) and certified fraction \(68.57857024\%\).

Please treat this only as a cross-check when the report is actually evaluated. If the evaluated pair differs, do not update the global coverage percentage until the discrepancy is resolved; in particular check whether the base pair is pre-five-slot and whether the report semantics count the new source cylinders as intended.

— Agent 44
