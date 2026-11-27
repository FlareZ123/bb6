# Raw40: local canonical coverage and outstanding obligations

Parent `1RB---_1RC---_0RD---_1LD1LA_------_------`, first unassigned A1 query after six ordinary transitions. The whole parent remains open. The original two-query canonical frontier contains 189 five-hole representatives; this is not the global cryptid roster. See the [historical evidence and individual child results](Raw40-history-pre-20261127.md) for earlier exact witnesses, compiler evidence and local refinements. The global accepted interface is maintained in the repository root README, independently of this dossier.

## Six-hole family status

| A1 | Weighted maximum | Status and source |
|---|---:|---|
| 0RC | 888 | Locally kernel accepted: [consumer](Raw40A0RC.lean), [rebuild](reproduce-A0RC.sh) |
| 0RD | 1132 | Locally kernel accepted: [consumer](Raw40A0RD.lean), [rebuild](prepare_a0rd.py) |
| 1RC | 5729 | Source accepted [CI 45854063610](https://github.com/FlareZ123/bb6/actions/runs/45854063610), [consumer](Raw40A1RC.lean) |
| 0RB | 637 | Candidate, several child proofs accepted; full consumer pending |
| 1RB | 1130 | Candidate, full consumer pending |
| 0LB | 75493794 | Complete certificate candidate, [CI 45939992957](https://github.com/FlareZ123/bb6/actions/runs/45939992957) pending |
| 1LA | 790 | Complete certificate candidate; [grammar accepted](https://github.com/FlareZ123/bb6/actions/runs/45943030210), [aggregate CI 45943412131](https://github.com/FlareZ123/bb6/actions/runs/45943412131) pending |

The maxima are weighted first-hole scores in the repository convention; only an accepted universal consumer and attainment establish exactness. Other A1 families remain incompletely classified. None of the local bounds is a claim that BB(6) is solved.

## A1=1LA: full nine-child candidate

| B1 | Open leaves | FAR | Compact | Grammar | Weighted maximum candidate |
|---|---:|---:|---:|---:|---:|
| 0LC | 447 | 431 | 16 | 0 | 94 |
| 0LE | 1948 | 1849 | 99 | 0 | 498 |
| 0RC | 914 | 890 | 24 | 0 | 325 |
| 0RE | 3761 | 3585 | 173 | 3 | 702 |
| 1LB | 1010 | 999 | 11 | 0 | 107 |
| 1LC | 600 | 592 | 8 | 0 | 92 |
| 1LE | 2191 | 2118 | 73 | 0 | 644 |
| 1RC | 1433 | 1354 | 79 | 0 | 161 |
| 1RE | 5818 | 5616 | 202 | 0 | 790 |
| Total | 18122 | 17434 | 685 | 3 | 790 |

Attainment candidate `1RB1LA_1RC1RE_0RD1RC_1LD1LA_HHH0LF_1RC1LF`: 789 ordinary steps, halt, no delay. [Full consumer](Raw40A1LA.lean), [partition](Raw40A1LABase.lean), [generator](prepare_a1la.py), [rebuild](reproduce-A1LA.sh). Discovery banks `a1la-<B1>-discovery.json` retain exact literal tables and certificate data, so rebuilding does not rerun FAR discovery. The three special machines are proved by a variable-length unary-run grammar, not a cutoff or an affine-growth extrapolation; see [proof](A1LA-unary-grammar.md) and [Lean source](Raw40A1LAUnaryGrammar.lean). The three original-source nonhalting proofs passed Lean 4.36.0-rc2 in CI 45943030210. All aggregate claims remain candidates until checked.

## A1=0LB: delayed halt and nonhalting certificates

[Late witness and hard leaves](A0LB-hard-leaves.md), [full candidate consumer](Raw40A0LB.lean), [generator](prepare_a0lb.py), [rebuild](reproduce-A0LB.sh). B1=1LB leaf561 reaches E0 at exactly 75,493,793 ordinary steps and attains weighted score 75,493,794 if E0 halts. The prior individual Lean proof is accepted; its enclosing family is not yet accepted. The accelerated checker avoids evaluating all 75 million steps in the canonical audit.

B1=1RE leaf198 has a compact 16/17 asymmetric n-gram certificate candidate with 2229 reachable configurations, 95 left and 581 right summaries and 735 predecessor edges; [data](a0lb198-compact.json). All 39 lag-bank leaves have finite closure candidates. These exploit lag-XOR followed by bounded run/residue summaries; exact tables and graphs are saved. The three multi-hole late queries are expanded rather than treated as nonhalting.

## A1=1LC B1=0LC: new five-hole candidate

All 122 initial opens have evidence: 105 FAR, 14 compact, and three [exact periodic-sweep mathematical proofs](A1LC0LC-periodic-sweeps.md). Candidate exact weighted score 106, with attainment at 105 ordinary moves plus halt, delay 0. [Lean recurrence source](Raw40A1LC0LCPeriodic.lean), [candidate exactness](Raw40A1LC0LCExact.lean), [generator](prepare_a1lc_0lc.py). This is not yet kernel accepted.

## Reusable mechanisms and baseline

[Portable canonical enumerator and compact closure](discover_compact.js), [FAR search](far_search.js), [compact Python emitter](compact_ngram.py), [graph minimizer](minimize_compact.js), [modular certificate integration](certify_modular.py). The trusted Lean checker independently reconstructs closure from supplied graphs. An accepted small graph is not itself an accepted parent audit: every canonical branch, early halt, late query and attainment must be included.

Three previously established five-hole pump families have exact entries and costs: 0LA/C1=0RC (entry9, 3n+2, 6n+13); 1LA/B1=0RD (entry8, 2n+3, 8n+17); 1LA/B1=1RB (entry8, 4n+3, 8n+15). See [Raw40Pump](Raw40Pump.lean), [Raw40MorePumps](Raw40MorePumps.lean). The unquotiented 303-cylinder frontier and 189-entry canonical frontier are distinct representations. The accepted local refinements must be composed through a checked consumer, not subtracted informally.

Next: accept the two complete candidate family audits, resolve any actual compiler failures, then continue the remaining A1 families. Rebuilds use Lean 4.36.0-rc2 and the original Canonical77 dependency artifact 14997966221.
