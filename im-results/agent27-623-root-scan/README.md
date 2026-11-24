# Source-faithful #623 root gap/scale scan

This directory contains a dependency-free JavaScript BigInt replay of the high-level section map for the six-state machine

~~~text
1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA
~~~

It is a finite computational diagnostic, not a nonhalting proof.

## Reproduction

Requires Node.js with BigInt support:

~~~bash
node im-results/agent27-623-root-scan/RootGapScaleScan.js 20000
~~~

The script is pinned to google-deepmind/cryptids at commit c86f15861709b76042998c5211c7b2f83991621b, file BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean. It implements the source equations for evalA, drainB, and highLevelNext using BigInt. Crucially, the r=1,a>0 case of evalA recursively continues with A(a-1,j,m+2*j+3); it must not return the intermediate tuple as a completed D3 state.

The script asserts the first 20 source-trace states whenever at least 20 transitions are requested, and it includes fixed regression assertions for the 20,000-step summary. The recurrence and metric implementation was executed inline in the V8 runtime. The committed Node.js CLI wrapper has not yet been run under Node in this invocation because the local shell was unavailable; run the command above once in a functioning Node environment before treating the standalone wrapper as independently smoke-tested.

## Exact ell=20 cone-family root exclusion

[ConeOnlyEll20RootExclusion.md](ConeOnlyEll20RootExclusion.md) and its
Lean source [ConeOnlyEll20RootExclusion.lean](ConeOnlyEll20RootExclusion.lean)
formally enumerate the three members of the all-depth cone-only family at
mass depth 20, identify their exact original-source transitions, and exclude
all six endpoints from the authentic blank-root orbit using Agent 41's
adjacent root-mass gaps. This closes only the ell=20 slice, not the
all-depth family or machine #623.

## 20,000-transition result

The 20,000-step run in the V8 runtime produced:

| Diagnostic | Exact/observed result |
|---|---:|
| transitions | 20,000 |
| checked indices | 9 through 19,999 |
| side-selection mismatches | 0 |
| zero ratio-four gaps | 0 |
| minimum root gap slack | 65 |
| minimum-slack state | index 14, D(314,385), h=71, m=314 |
| minimum abs(g)/m | log2 = -12.960451552003178, index 6,899 |
| minimum g^2/m | 4096/235, log2 = 4.123483053435001, index 16 |
| maximum abs(eg)/ternaryDigits(m) | 102/4 = 25.5, log2 = 4.672425341971495, index 11 |
| maximum abs(em)/ternaryDigits(m) | 24/4 = 6, log2 = 2.584962500721156, index 11 |

For a state D(a,d):
- m = min(a,d);
- g = a-4d when a >= d, and g = d-4a otherwise;
- (gNext,mNext) = (g-9m,3m) when g > 0, and (-4g-9m,3m+g) otherwise;
- eg = actual gNext minus predicted gNext;
- em = actual mNext minus predicted mNext;
- ternaryDigits(m) is the base-3 digit count of m.

The minimum-slack calculation is exact: for m > 0, ceil(log_3(2*m+1)) equals the number of base-3 digits of 2*m. Thus the slack is abs(a-d) minus that digit count. At index 14 this is 71-6=65.

The first 20 root states emitted by the script are:

~~~text
D(0,7), D(6,14), D(6,31), D(26,26), D(2,83), D(84,10),
D(74,38), D(30,138), D(108,101), D(2,321), D(322,10),
D(312,38), D(268,138), D(122,438), D(314,385), D(74,950),
D(876,235), D(632,735), D(104,1914), D(1808,329)
~~~

## Observed sector/phase structure

For root states at indices 9 through 19,999:

| Sector | Visits | Minimum slack | State attaining minimum |
|---|---:|---:|---|
| right-odd | 5,878 | 65 | index 14, D(314,385) |
| left-even | 4,013 | 124 | index 12, D(268,138) |
| right-even | 5,877 | 310 | index 13, D(122,438) |
| left-odd | 4,223 | 452 | index 20, D(1472,1013) |

Across the 19,991 transitions from state index 8 to state index 19,999, only these branch-label edges occurred:

| Edge | Count |
|---|---:|
| left-odd -> right-odd | 2,633 |
| right-odd -> left-even | 2,581 |
| left-even -> left-even | 1,432 |
| left-even -> right-even | 2,580 |
| right-even -> right-odd | 3,245 |
| right-odd -> right-even | 3,297 |
| right-even -> left-odd | 2,632 |
| left-odd -> left-odd | 1,591 |

This is a finite observed phase graph, not a proven transition restriction. The sector-specific slack minima are also only empirical. Failed tests of coordinate residues, drain counts, sector histories, quotient-path suffixes, and simple 3-adic valuations are consolidated in PhaseSearch.md. For example, the synthetic state D(2,69) is right-odd with slack 65 but maps to D(70,10), whose left-even slack is 57. The data may nevertheless help formulate a root-history invariant that distinguishes the blank-root orbit from arbitrary cone states.

Agent 32 independently archived a second 20,000-step Node BigInt scan at im-results/agent32-623-gap-slack/scan.mjs. It asserts the first 17 root states through D(876,235), checks newAffineCone membership at every state from index 9 onward, and asserts generic six-slack counterexamples. The two independent Node implementations agree on the reported root metrics.

## Relationship to the older C++ diagnostic

The older im-results/agent8-623-inverse/root_gap_scale_scan.cpp has a source mismatch in its evalA implementation: its r=1,a>0 branch returns instead of continuing the recursive A-evaluation. Its current checked-in code therefore cannot produce the 20,000-step output above. The JavaScript replay independently reproduces the historical numeric metrics using the pinned Lean equations; the old C++ file still needs repair before its own output can be trusted.

## Interpretation and limitations

The 20,000-step result is empirical evidence only:
- zero mismatches over a finite prefix does not prove the branch-selection rule for all future states;
- the observed 65-slack inequality is not forward-invariant for arbitrary states (for example, D(2,69) -> D(70,10) loses slack); it does not even guarantee one-step cone preservation: D(18,88) has slack 66 but maps to D(70,65), which is outside newAffineCone;
- no all-time root-history invariant has been established;
- this does not prove that the machine is nonhalting and does not resolve any BB(6) holdout.

The useful next mathematical task is still to derive a root-specific inductive/cocycle invariant that keeps the blank-root orbit in the source-certified newAffineCone after its finite entry prefix.


## Source-derived boundary phase bridge (Agent 32)

The independent phase extraction is now maintained at [Agent 32's actual boundary phases](../agent32-623-phase-automaton/ActualBoundaryPhases.md), with the complete machine-readable phase set in [ActualBoundaryPhases.json](../agent32-623-phase-automaton/ActualBoundaryPhases.json). It recomputes the exact carry entering digit (k+1) from the parity-correct drain statistics and source (C,F) correction table over the existing 9,968-state interval (n=33\ldots10000). The affine update agrees with this high-level recurrence at every checked state, and the sector update agrees at every state.

There are 262 observed complete phases (114 L, 148 R); ignoring sector, 30 L and 40 R previous-digit/carry states. Actual carry pairs are L ({(-2,1),(-1,0),(-1,1),(0,0)}) and R ({(-3,1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(0,0)}). The phase alone is not deterministic (maximum observed successor count 25), so it is not an all-time invariant. The same directory contains the 263-state reset-pattern DFA and explicit raw-language nonclosure witnesses. These are phase diagnostics, not a new root-horizon scan or a nonhalting proof.

This README remains the canonical source-faithful root trace; Agent 32's independent 20,000-step replay is the cross-check already cited above. Do not create another root scan or promote the observed sector graph to a theorem.


## Recurrent obstruction reduction

[NonSynchronizingSCCs.md](NonSynchronizingSCCs.md) gives an exact SCC decomposition of the 211-state paired-carry subset automaton. It isolates the ten recurrent nonsynchronizing components (83 states) and proves a four-symbol transient bound from the full 66-state uncertainty set. This is an automaton-level reduction; excluding these ten bad-tail languages on the authentic S-window stream remains open. Reproduce with [analyze_non_sync_sccs.js](analyze_non_sync_sccs.js).


## Conservative S-window residual map

[ConservativeSWindowResidualMap.md](ConservativeSWindowResidualMap.md) records the 9,968-window scan under the conservative buffer. It finds 81 nonsynchronizing post-reset suffixes, all at or before D(5580), followed by 4,421 consecutive rank-one windows through D(10001). This is finite evidence, not an all-time invariant. Reproduce with [analyze_conservative_s_window_residuals.js](analyze_conservative_s_window_residuals.js).


## Retraction: ConservativeSWindowResidualMap

The ConservativeSWindowResidualMap scan is retracted for exact S-window research. It used the superseded buffer and a mismatched q-window carry phase. Do not use its 81-exception threshold, product collisions, or buffer conclusions. Use the correction-only S-window phase script at [agent48](../agent48-623-tight-window/s_window_boundary_phases.js), the shift theorem at [MonotoneMassWindow](../agent41-623-3euclidean/MonotoneMassWindow.md), and the valid [SWindowPostResetSynchronization](SWindowPostResetSynchronization.md) result with 84 exceptions.
