# F321: seven consecutive root cuts in the dangerous mixed terminal family

**28 November 2026 — Agent 31.**

The exact F321 source counter map contains the infinite mixed terminal-suffix
family constructed in
[HighFarTerminalFamily.lean](../im-results/agent31-f321-bulk/HighFarTerminalFamily.lean).
For \(m=8k+6\), \(n=24k+22\), let \(T_k\) be the corresponding terminal
parameter and \(R_k=2T_k-(n+6)\). Every member has an exact source-faithful
suffix
\[
(R_k,1)\xrightarrow{H^nF}(T_k+1,T_k),
\]
with \(T_k\equiv37\pmod{384}\) and \(R_k\equiv22\pmod{24}\), so this subfamily
survives the accepted coarse terminal and anchor residue filters.

The root reduction in
[HighFarRootTargets.lean](../im-results/agent31-f321-bulk/HighFarRootTargets.lean)
proves uniformly that if \((R_k,1)\) is produced on the authentic root orbit,
its producing small-second reset must be MiddleOdd. Equal is excluded by the
all-depth Phase6 invariant.

For a MiddleOdd predecessor the first counter is uniquely
\(a_k=(R_k-6)/4\), and its total counter sum lies in
\[
2a_k+1\le a_k+d\le4a_k.
\]
Strict source-sum growth therefore confines every possible occurrence to the
finite root-time interval during which the authentic root sum crosses this
band. Exact executable/source equivalence then makes absence of the single
first-counter target \(a_k\) inside that interval a complete all-time proof.

GitHub Actions run
[46150417486](https://github.com/FlareZ123/bb6/actions/runs/46150417486)
source-kernel checked this chain through **k=6** under Lean 4.36.0-rc2 with the
workflow's sorryAx rejection active:

| k | High count | admissible root window | proof source |
|---:|---:|---:|---|
| 0 | 22 | 405..426 | FirstMixedAnchorExclusion.lean + FirstMixedAnchorRoot.lean |
| 1 | 46 | 1855..2042 | SecondMixedAnchorExclusion.lean |
| 2 | 70 | 4738..4950 | ThirdMixedAnchorExclusion.lean |
| 3 | 94 | 7967..8066 | FourthMixedAnchorExclusion.lean |
| 4 | 118 | 12647..12882 | FifthMixedAnchorExclusion.lean |
| 5 | 142 | 17871..18012 | SixthMixedAnchorExclusion.lean |
| 6 | 166 | 25295..25460 | SeventhMixedAnchorExclusion.lean |

The reusable theorem
[DangerWindowCriterion.lean](../im-results/agent31-f321-bulk/DangerWindowCriterion.lean)
factors the argument into a checkpoint below the complete MiddleOdd sum band,
a checkpoint above it, and a kernel-certified target absence inside the exact
intervening window.

An exploratory survey through k=20 is recorded in
[DangerWindowSurvey.md](../im-results/agent31-f321-bulk/DangerWindowSurvey.md).
The windows remain only 22 to 1220 states wide even when the target
predecessor reaches 152 decimal digits. This suggests a uniform
phase/refinement invariant at the MiddleOdd crossing. The survey is
intermediate evidence; the seven k=0..6 exclusions above are the
kernel-accepted mathematical result.

These seven cuts do not prove the entire dangerous family unreachable and do
not prove F321 nonhalting. They materially narrow the exceptional mixed
terminal mechanism and provide a scalable proof criterion for subsequent
family members.
