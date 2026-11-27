# Reset-capable right-scan quotient within Box28

**Status:** **Original-source Lean acceptance achieved** in [46075711833](https://github.com/FlareZ123/bb6/actions/runs/46075711833), artifact [15234559720](https://github.com/FlareZ123/bb6/actions/runs/46075711833/artifacts/15234559720), SHA256 `5414e58e54164aa628486ecf98d59d9963b9a897e77631b909149b9f4ceffacb`. The source theorem `BB6.Agent17.Box28TransducerSource.rectangle_bound` covers the full 194,400-table subfamily at weighted bound 51. It is a strict extension of the 6,075-table all-write-one scan quotient. This is a subfamily of D0=18/E0 cuts, not a whole cut or global roster subtraction.

Use the existing table codes: 0=halt, 1+4q+2w+d with d=1 for right. Fix A0=8,B0=11,C0=11,C1=13,D0=18,D1=15. The five slots A1,E1,F1,E0,F0 independently take the six rightward moves to A,E,F, with either write bit; B1 is arbitrary. Thus 6^5×25=194,400 tables, with 7,776 core parameters. The six codes map to literal table codes [2,4,18,20,22,24].

## Exact macro and quotient

At the E scan root, the right tape is 1^n01 followed by blank; the left tape begins with zero, beyond which the frame is arbitrary. Scan the n ones, tracking (state, number of trailing written ones). A rightward zero write resets that number to zero, while a one write increments it. If the scan ends in A, A0 consumes the gap and immediately queries B1. Otherwise consume the gap and marker, then follow the rightward zero transitions until A, or drift forever. A return to A induces the fixed B0/C1/D1/D0 rewind sequence; its exact new unary length is the trailing write count m. If the intervening gap/marker/zero path has length l (2≤l≤4), the positive return cost is n+l+m+4 live transitions. The untouched left tail remains arbitrary beyond its last zero. See `Box28TransducerModel.lean` for the parametric stream proof.

A deterministic three-state scan is on a cycle of length dividing six after at most two transitions. Over an additional six transitions in that cycle, the trailing counter either grows by six (all writes one) or becomes independent of its original value (a zero resets it). At n≥8, in the all-one case its count is at least n−2; the following l≥2 moves either reset it or produce an output ≥8. Consequently the exact macro outcome (B1 query, infinite zero drift, or next length class) is congruent under the 14-class map n↦n for n<8 and n↦8+(n−8) mod 6 otherwise. The previously committed `Box28Transducer.lean` gives the corresponding `step_class` proof using a finite 216×6 cycle check and induction for arbitrary multiples of six. A 15-vertex orbit suffices for a closed safe bank. There is no maximum concrete tape-length assumption.

## Finite classification

| Outcome | Core parameters |
|---|---:|
| Repeated safe quotient class | 3,764 |
| Infinite zero drift | 2,989 |
| B1 query | 1,023 |
| Total | 7,776 |

The 6,753 safe cores give 168,825 nonhalting completions for arbitrary B1. In the 1,023 query cores, the only possible halt is at B1; B1=halt has the recorded primitive live count plus one halt transition, and all other completions contain no halt instruction. Maximum ordinary score is 51, attained by both parameter tuples (3,5,0,1,1) and (5,0,3,1,1). One explicit maximizing machine is [8,20,11,0,11,13,18,15,4,24,4,2]. The independent `transducer_check.py` verifies all 1,023 literal primitive halt witnesses and 139,968 sampled period comparisons. The latter comparisons are a sanity check, not the proof of the all-length quotient.

The new source module uses the existing exact source projection, verifies every finite B1 prefix via the original reflective last-hole checker, and proves the weighted bound for all compatible machines. The aggregate finite checks are split into small kernel-reduced batches. The witness is independently checked by zipHalt_sound. No native_decide. Local Lean 4.36.0-rc2 works, but the checkout cannot be obtained through local git (DNS failure); a copied arithmetic subset gave the exact counts and a representative 36-pair kernel check with [propext, Quot.sound]. The full finite aggregate, exact source import closure, rectangle bound, and attaining witness passed the combined source audit on commit d063f0c0981e13df023c6e70cb639a5688f72d18. Exactly 1,023 complete labeled tables halt and 193,377 do not, by the independent classification and the single possible halt slot. The family is not a complete first-hole cut.
