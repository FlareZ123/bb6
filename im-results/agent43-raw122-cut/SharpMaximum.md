# Raw122 sharp maximum and two exceptional halters

**Status:** M0's exact attained score and the sharp 0LF child bound were locally source-checked in the previous incarnation (commits f4c5681cab17da70c4650b0570a181945026a9de and ad45915b1f830acc348077041b02daea70919bd9). All 24 ordinary child bounds are separately source-accepted at the earlier cutoff 6,766,859, with 20 at 7,014. The joint parent import closure remains unaccepted. The new exception-preserving source modules described below are **locally source-accepted at the leaf and exceptional-child levels; the joint parent awaits its dependency closure**, not a newly accepted parent Cover.

Parent partial machine (canonical index 86): `1RB---_1RC---_0RD---_1LD1RE_---0LF_------`.

## Exact late-query witnesses

| Completion (--- denotes halt) | Primitive halting score | Realizable blank delays | Largest weighted score |
| --- | ---: | --- | ---: |
| `1RB---_1RC0RA_0RD0LF_1LD1RE_0RB0LF_1LC0LF` (M0) | 6,659,487 | 0 | 6,659,487 |
| `1RB0LA_1RC---_0RD0RB_1LD1RE_0LA0LF_1LB1LE` (M1) | 1,296,925 | 0, 1 | 1,296,926 |

The original packed runs establish ordinary-prefix lengths 6,659,486 and 1,296,924. Each late-query cylinder has exactly one unassigned row (A1 or B1 respectively); filling that row with any ordinary instruction makes every row ordinary, so the table cannot halt. Filling with halt gives the unique halting completion of each cylinder. M1's E0 is a zero-writing transition to A, which realizes the additional incoming delay of one; M0 has no such incoming zero-writing transition. The independent [literal replay](top_two_replay.py) reproduces both final queries, head positions and visited-cell counts without trusting the packed emitter.

## Stronger classification from the accepted child rosters

The twenty ordinary small-cutoff child certificates already use 7,014. The remaining 0LA and 1LF rosters contain only nonhalting residual witnesses; their audits use 7,014. Their sharper bounds at 7,014 now pass local Lean against the archived original-source dependency closures (`Raw122Sharp00.lean`, `Raw122Sharp17.lean`). The 0LF roster contains nineteen nonhalting tables and one M0 cylinder; the 1LE roster contains twelve nonhalting tables and one M1 cylinder. The first F1 halt branch is handled by the original root split at step 7. Thus, **at the level of the written proof from the separate source certificates**, every compatible completion except M0 and M1 has weighted halting score at most 7,014. Unlike a uniform bound, retaining the actual residual-table identities shows the two exceptional machines are the only possible weighted halters above that cutoff. It also implies uniqueness of the maximizer, and the exact runner-up maximum 1,296,926 after excluding M0. The ordinary physical runner-up score is 1,296,925.

This is a sharper mathematical conclusion for the 25^6 literal completions than the existing uniform sharp upper-bound draft. The reasoning uses the original `partialSound` alternative (audit bound or compatible residual), not a simulation assumption about any unresolved table. The strengthened joint source proof is staged in:
- [Raw122ExceptionalLeaves.lean](Raw122ExceptionalLeaves.lean): reusable one-hole uniqueness lemma, M1 attainment and exclusion of other halting completions.
- [Raw122Exceptional05.lean](Raw122Exceptional05.lean) and [Raw122Exceptional16.lean](Raw122Exceptional16.lean): source-checked pointwise use of the exact 0LF and 1LE residual rosters, retaining each exceptional machine. [Raw122ExceptionalBranches.lean](Raw122ExceptionalBranches.lean) imports both.
- [Raw122TopTwoCore.lean](Raw122TopTwoCore.lean): parent exception bound and exact weighted maximum and runner-up equivalences, source-checked conditional on the exact pointwise `ChildExcept` interface. [Raw122TopTwo.lean](Raw122TopTwo.lean) supplies that interface from the 24 accepted child proofs, pending the full import closure.
- [Raw122SharpParent.lean](Raw122SharpParent.lean): prior uniform exact-maximum theorem draft, still the direct sharp Cover target.

The exact original-source leaf and both exceptional-child modules passed local Lean 4.36.0-rc2 against the accepted archive closures, including artifact 15139277002, repack 15140660301 and the 24 branch16 shard artifacts plus assembly 15119068714 from run 45818787152. `cover05_except` and `cover16_except` use only propext, Classical.choice and Quot.sound; the one-hole uniqueness theorem uses propext and Quot.sound. The independent literal replay also passed. Direct repository checkout failed DNS resolution, so archive reconstruction supplied the dependencies. Agent40 is already recovering the archived parent closure; do not rerun a large independent closure merely to compile these small consumers. Link the new modules after that existing proof closure is assembled. The global BB(6) status and Canonical59 roster are unchanged.
