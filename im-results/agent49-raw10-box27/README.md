# Raw10 Box27: exact 128-child source quotient

**28 November 2026.** **Update 18:06 UTC:** the E0=22 full-source check succeeded, and the corrected D17 parent plus its E/F conjugate have been locally kernel-checked. The current exact source frontier is 128 representative six-hole child obligations; see [SYMMETRY_FRONTIER.md](SYMMETRY_FRONTIER.md). The historical E0 work below documents the construction. The source domain is `raw10Remainder[27]!` with A0=8, B0=11, C0=C1=13. This dossier fixes D0=14 and D1=17 and then partitions **all 25 possible E0 codes**. A1, B1, E1, F0 and F1 are unrestricted in each branch, so each whole E0 cylinder has `25^5 = 9,765,625` complete tables. The full fixed-D0/D1 family has **244,140,625** tables. All stated scores use the repository's original-source weighted convention.

## Accepted mathematical boundary

| E0 code(s) | Bound or exact weighted maximum | Original-source accepted evidence |
| --- | ---: | --- |
| `0,1,2,4..20` (20 distinct values) | bound 108 | [CI 46092810166](https://github.com/FlareZ123/bb6/actions/runs/46092810166), `Box27EasyE0.source_bound` |
| `21` | **exact 108** | [CI 46092558221](https://github.com/FlareZ123/bb6/actions/runs/46092558221), `Box27Slice.exact_weighted` |
| `3` | **exact 141** | [CI 46094172421](https://github.com/FlareZ123/bb6/actions/runs/46094172421), `Box27Slice03.exact_weighted` |
| `23` | **exact 143** | [CI 46094175250](https://github.com/FlareZ123/bb6/actions/runs/46094175250), `Box27Slice23.exact_weighted` |
| `24` | **exact 255** | [CI 46094310742](https://github.com/FlareZ123/bb6/actions/runs/46094310742), `Box27Slice24.exact_weighted` |
| `22`, **excluding one 25-completion table** | exact 149 on the restricted subset | [CI 46094538498](https://github.com/FlareZ123/bb6/actions/runs/46094538498), conditional `Box27Slice22.exact_weighted` |

These source-accepted results classify **244,140,600 distinct tables** (every completion in the fixed D0/D1 family except the 25 completions of `[8,24,11,8,13,13,14,17,22,15,4,-1]`), all at weighted bound 255 or below. The E0=24 witness `[8,21,11,18,13,13,14,17,24,0,3,6]` halts in 254 live moves and scores 255. These are disjoint per-E0 results, **not yet one kernel-consumed parent theorem**. The largest bound for the 25 exceptional completions is not established by the accepted prior certificates.

## New 10-state/side finite automaton for the exceptional 25 tables

`Box27ExceptionalFAR.lean` contains a concrete two-sided stack automaton with **10 states per tape half and 306 reachable abstract control/stack states**. Its closed state relation contains no F1 query, so the generic original `TwoSidedAutomata.never` theorem would prove that every F1 completion runs forever. `generate_exceptional_far.py` reconstructs the table, both stack relations and the abstract reachable set from a three-state transformation monoid and a three-bit prefix automaton. The search algorithm is *untrusted*; Lean checks the entire finite certificate by `BB6.Agent4Automata.check`.

The exact table-identity bridge `Box27Slice22.exceptional_far_table` is added to `Box27Slice22Core.lean`; `generate_slice22.py` now emits `all_bound` and `full_exact_weighted` at **149** without the exceptional hypothesis. A focused original-source [CI run 46113905945](https://github.com/FlareZ123/bb6/actions/runs/46113905945) succeeded; its original-source artifact was used in the local parent proof.

The next source file `Box27D17Parent.lean` combines all 25 E0 values under their exact original Raw10 domain, with theorem
`BB6.Agent49.Box27D17Parent.exact_weighted`, intended to prove **sharp weighted maximum 255 across all 244,140,625 tables**. Existing manual [CI 46114149252](https://github.com/FlareZ123/bb6/actions/runs/46114149252) was cancelled. The fixed parent theorem has now compiled locally with the actual accepted child artifacts and no sorryAx; see the current symmetry dossier.

## Source mechanisms

The first-hole subtree emitters `generate_slice.py`, `generate_slice03.py`, `generate_slice22.py`, `generate_slice23.py`, and `generate_slice24.py` regenerate finite halt witnesses, side-cycle witnesses, last-hole checks and two-sided finite-stack automata. The `Box27Slice*Core.lean` modules prove that accepted leaves imply the original blank-start bound. The exceptionally structured E0=22 children can also invoke `Box27MaskedCounter3.never`, accepted in [CI 46093466147](https://github.com/FlareZ123/bb6/actions/runs/46093466147), rather than relying on finite simulation. See [MASKED-COUNTER.md](MASKED-COUNTER.md) for the carry/unwind grammar.

An independent, smaller unary-growth cylinder `[8,3,11,2,13,13,14,17,21,-1,3,-1]` is covered by the E0=21 complete theorem, but retains a useful explicit recurrence: at primitive time 5, the machine is at rightmost marker `R(0)`; from `R(k)` it reaches `R(k+1)` in `10+4k` steps, hence `R(k)` occurs at time `2k²+8k+5`. The run never queries E1 or F1. `Box27GrowingBlock.lean` and `Box27GrowingBlockSource.lean` are an alternative paper/Lean candidate proof, **not** a new disjoint parent reduction.

## Remaining proof obligations

1. Accept and axiom-audit the one-hole FAR plus **unconditional** E0=22 full-source theorem.
2. Accept the complete D0=14/D1=17 parent join, including its source-domain `Fits` witness, without re-searching the already accepted child certificates.
3. Integrate this local bounded cylinder into the live Raw10 parent complement; other D0/D1 values remain open. The fixed-D17 result is not an unconditional Raw10 Cover and proves no global BB(6) upper bound.
