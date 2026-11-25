# Raw60 partial closure

Raw residual 60 (canonical index 36), E1=1RA, parent `1RB---_1RC---_0RD---_1LD1RE_---1RA_------`, six holes. First hole A1 after seven ordinary transitions.

## Source-accepted children

[CI run 45526080641](https://github.com/FlareZ123/bb6/actions/runs/45526080641), pinned head 68130504c543e151395a29a0fde7a4be1e50e765, passed both raw60 jobs and the forbidden-axiom guard. Each generated `BB6.Agent1Raw60A{move}.all_closed` is a weighted upper-bound theorem for every compatible completion of its exact child. The generators retain the complete first-hole tree, and use source-checked side cycles, last-hole rules, FAR and universal pumps.

| A1 | Bound | Splits | Side cycles | Last-hole leaves | Open leaves discharged | Accepted job |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| 0RC | 376 | 821 | 15133 | 3525 | 226 | 138909656398 |
| 0RE | 719 | 526 | 9265 | 2713 | 121 | 138909656912 |

These are disjoint cylinders, each of mass 25^5=9,765,625. The raw60 certificate generator and its exact specs are maintained in this directory.

## Source-accepted conditional reductions

[CI run 45527307533](https://github.com/FlareZ123/bb6/actions/runs/45527307533), pinned 3df652a97562f6f7457708cafcb8d65054d36b57, passed both conditional child audits and the root split. `Raw60RootCut.lean` proves every compatible completion of the parent has weighted bound 1175 or lies in one of eleven explicitly named residual A1 children, using the accepted 0RC and 0RE bounds as premises. Eleven immediate side-cycle children and the initial halt branch are also discharged.

| A1 | Weighted bound conditional on exceptions | Remaining exact tables (global open-list index) |
| --- | ---: | --- |
| 0LD | 176 | 1488 |
| 0RF | 1175 | 4335, 4336 |

These conditionals do not establish an unconditional bound for either child. The previously late unassigned transition of 4338 is closed by a last-hole witness at step 1169. All four recursive proofs below are now source-accepted. The parent itself remains open.

## Further mathematical reductions

For global open-list entries 1398/1399, the shared binary-block proof `Raw60LDBinary.lean` proves for arbitrary untouched tails L,R that D((00)^(n+1)11L,R) reaches F with identical tapes. Cost T(0)=8; T(n+1)=2T(n)+8 or +10 according to F1=0LD/0LE. From blank time 2 the C-family grows two zeros per epoch.

For entries 1676/1677, `Raw60LDTernary.lean` proves an arbitrary-tail recursive traverse F(1^(3n+k)0L,R) -> B(0 1^(3n+k-1)0L,R), k=2 or 1, cost T(n+1)=2T(n)+26. Exact blank entries at t=18 and t=74 give an E-boundary family growing three ones each epoch. Both local operational-model checks and the original-source conditional child audit passed, including their blank-entry and nonhalting wrappers.

## Reproducible candidate frontier

The existing agent2-tnf-raw99/enumerate.cpp on the parent (cutoff 1000, side-cycle window 256) gives 14,534 splits, 252,125 side-cycle leaves, 69,602 last-hole leaves, 12,556 open leaves. Masses: cycle 220,279,925; halt 18,679,552; total-defined 1,670,448; open 3,510,700; total 244,140,625 = 25^6. Open-list SHA256 f99d4f305af5f37284edca62fa8ceba353ea363d67fd839f7933a47b092ee25a. Maximum weighted score in this finite census is 929 (928 ordinary transitions, zero incoming delay), table `1RB1LF_1RC0LB_0RD0RF_1LD1RE_HHH1RA_1RC1LB`.

The pooled bank (agent11-raw107, agent3-tnf-raw120, agent8-tnf-six/raw115 and raw119) contains 431 distinct valid numeric DFA codes of at most ten states, with first DFA symbol zero. The agent11-raw107/bank.cpp saturation checker finds 11,664 candidates, leaving 892. Enumerating 20,225 normalized five-state DFAs (plus the smaller sizes) finds 60 more, leaving 832 before pumps. A million-step simulation of these 832 finds one late unassigned transition (global index 4338, step 1169, E0) and 831 still open. A new [two-sided window checker](../agent1-ngram/README.md) finds 423 additional candidate certificates at width at most ten (332 at width at most seven) among the 832 post-FAR misses. Four pilot certificates have passed source checking. Nine further candidates at width 11–12 are not yet prioritized because of their larger proof cost. The census and unaccepted certificates are discovery results, not proof of the remaining cylinders' bounds.

Reproduction: compile enumerate.cpp with C++17/O3; run on the parent in a scratch directory; compile bank.cpp with C++20/O3; pipe zero-based open indices and underscore-free codes into bank with the pooled bank file. For accepted children use `python im-results/agent13-coverage/unpack.py`, `python im-results/agent1-raw60/generate.py 0RC 0RE` and the strict Lean closure compiler on `Raw60A0RCData.lean` and `Raw60A0REData.lean`.
