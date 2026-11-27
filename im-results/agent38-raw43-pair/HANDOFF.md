# Agent 38: Raw43 hard-pair handoff (2026-11-27)

**All six growth obligations are proved and source-verified.** CI [45990793759](https://github.com/FlareZ123/bb6/actions/runs/45990793759) compiled the exact eight-module closure; both `BB6.Agent38Raw43Octal.never` and `BB6.Agent38Raw43Run.never` passed the axiom audit (propext, Classical.choice, Quot.sound only). Artifact 15193284174. Source repair 6623826ba3df16d61d50d924675913316be7b85f. The old broad job 45974031217 stopped at runner shutdown before Raw43Run; its failure was not a counterexample or Lean error.

For M110/M202/M151/M243 use Raw43Octal.never with parameters (false,false), (false,true), (true,false), (true,true), respectively. For M355/M377 use Raw43Run.never with s=false/true respectively. The latter uses phase0--phase3, carry and terminal macros, Good invariant, and epochs budgeting 22 blank cells each. Its 4054-step entry starts with 150 padded zeros and reaches lowFront 4 (tail5 [0,0] 7) (zeros 89 ++ R) for arbitrary untouched R. Explicit Boolean lists and an endpoint rename lemma make the entry kernel-efficient.

Next: integrate the six exact literal tables via Agent25's growth mapping and accept the complete B1=1LA A1=0LA coverage proof. No global count change follows from these leaf theorems alone. Focused workflow target `raw43-hard-pair` is reproducible in agent10-four-hole.yml.
