# Global rooted zero-prefix classification

**Status:** intermediate exact combinatorial census and source-oriented proof-carrying partial frontier. BB(6) remains unknown. The exact correspondence between the census and the *decided mass* emitted by the Lean partial audit has not yet been kernel-proved. Elementary finite-control mathematics, no assertion of external novelty or a newly solved historical holdout.

## Exact raw-table theorem

Use the canonical six-state two-symbol universe with 12 entries and 25 actions per entry: one halt, 12 write-zero moves (two directions times six next states), and 12 write-one moves. The blank tape stays uniformly zero throughout any prefix of write-zero instructions, regardless of head motion. Thus it suffices to follow the deterministic read-zero transition of the current state, starting from A.

Stop at the first of three disjoint events: (C) a state is revisited after only write-zero instructions, implying perpetual nonhalting; (H) a halt is attempted after at most five prior moves, giving exact step score 1 through 6; (U) a first write-one instruction occurs, leaving all later evolution genuinely unknown.

For k distinct control states reached before the first event, where 1 <= k <= 6, define P_k = product over j=1,...,k-1 of 2(6-j). Every earlier transition must write zero and move to an unseen state, giving P_k directed control-path choices. On the kth state the terminal action has 2k returning write-zero choices, one halt choice, or twelve first-write-one choices. The other 6-k read-zero rows are arbitrary; all six read-one rows are arbitrary. Therefore the numbers of full tables in each class are:

- C_k = P_k * 2k * 25^(12-k);
- H_k = P_k * 25^(12-k);
- U_k = P_k * 12 * 25^(12-k).

These classes are disjoint, and no path can visit a seventh unseen state. The identity 25 = 2k + 1 + 12 + 2(6-k) yields a telescoping exhaustive partition of all 25^12 tables. No symmetry-quotient, dated cryptid census, one-halt normalization, or sparse-enumerator assumption enters the argument.

## Exact six-state census

Counts in these columns cover all SIX read-zero entries; multiply each entry by 25^6 to obtain all TWELVE-entry tables.

| Distinct states k | Cycle C | Halt H | First-one U |
| --- | ---: | ---: | ---: |
| 1 | 19,531,250 | 9,765,625 | 117,187,500 |
| 2 | 15,625,000 | 3,906,250 | 46,875,000 |
| 3 | 7,500,000 | 1,250,000 | 15,000,000 |
| 4 | 2,400,000 | 300,000 | 3,600,000 |
| 5 | 480,000 | 48,000 | 576,000 |
| 6 | 46,080 | 3,840 | 46,080 |
| **Total** | **45,582,330** | **15,273,715** | **183,284,580** |

Across all complete raw tables:

- **Nonhalting zero cycles:** 11,128,498,535,156,250 = 18.670522368%.
- **Halts with exact step score at most 6:** 3,728,934,326,171,875 = 6.256113664%.
- **Decided by this zero-prefix argument:** 14,857,432,861,328,125 = 24.926636032%.
- **First-write-one unresolved:** 44,747,211,914,062,500 = 75.073363968%.
- **Full raw universe:** 59,604,644,775,390,625 = 25^12.

## Reproducibility and formal scope

The C++17 checker [check-all.cpp](check-all.cpp) independently enumerates all 244,140,625 possible six-digit base-25 read-zero tables. It follows the actual path from state A, records the terminal event and distinct-state count, and compares all 18 counters with the symbolic formula above. In local testing a release g++ -O3 build completed the full exhaustive check in approximately 1.1 seconds. Read-one entries never affect the first event, so their 25^6 multiplier is exact.

The adaptive source module [ZeroPathAudit.lean](ZeroPathAudit.lean) imports the unmodified Agent8 finite-halt and zero-mask soundness oracles, and Agent4's genuine 25-way FrontierAudit and mass-conservation theorems. Unlike a fixed-slot enumerator it follows the current fully assigned write-zero path and branches at the first unassigned read-zero slot. It uses a formal theorem proving that slot is really unassigned. A branch can be certified only by the preexisting original-machine source oracle; all other leaves are explicitly open. It proves an all-table certified-or-open theorem and conserves total mass 25^12.

**Important boundary:** The exact census is a paper counting proof independently checked by exhaustive C++ enumeration. The Lean audit's theorem currently proves *total* mass conservation, plus soundness of whatever leaves it certifies. The stronger statement that this particular executable audit certifies exactly C+H full-table completions still requires a separate kernel-checked report evaluation or abstract coverage lemma. Until then, do not present the numeric decided fraction as a kernel-certified audit output.

This extends Agent42's previously counted A/0=0RB zero-only-cycle sector (2,605,108 of 25^5 residual read-zero rows) to the entire raw A-root universe and adds the exact early-halting sector. The underlying zero-mask soundness was already original-source proved by Agents8/44; this work provides a global census and an adaptive explicit-open partial audit. Neither result is an academically established new contribution to BB(6), so it belongs only in im-results.

For source verification use [manual workflow](../../.github/workflows/agent32-zero-path-global.yml), Lean 4.36.0-rc2, and review the actual run's head SHA and standard-axiom audit. The only local surrogate check was of Lean declaration interfaces; original-source compilation is the authoritative evidence.

## Remaining BB(6) gap

The 75.07% first-write-one sector retains all potentially complex blank-orbit behavior. This analysis does not decide those machines, establish an exact champion runtime, or close the universal bounded-score frontier. The existing original source bridges and sparse enumerator completeness still require end-to-end closure.
