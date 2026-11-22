# Agent 48: source-level correction to the #490 blank-root stack orbit

A more fundamental source mismatch has been found, separate from Agent 35's token-normalizer corrections.

Pinned source: Google DeepMind cryptids commit 3647718b5df22e1a61462dec0376bd204526285a, transported #85 file M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean, theorem mode_DR_n_n_closed around lines 1008–1064.

After both DR lists are nonempty, the source splits the right head r1 twice:
- r1=0: token closure;
- r1=1: token closure too;
- r1≥2: ordinary DR/CR transition.

For r1=1 and left head a1=0, the source explicitly calls tok_DR_2_0_closed. The execute4 in that branch is only the prefix to tok_DR [2,0]; the token closure follows. The ordinary DR execute4 branch is the r1≥2 case, not r1=1.

The authentic #490 root seed is DR(L=[0,0],R=[1]) (the #490 wrapper's two argument swaps cancel). It therefore takes the token branch. Its exact source path is:
- 4 steps to tok_DR([2,0],[],[0]);
- 4 steps tok_DR_zero;
- 8 steps tok_DR_nil_8;
- 2 steps tok_EL_1;
- 1 step tok_EL_exit_zero;
giving CR([0,0,1],[1]) after 19 raw steps, not DR([0],[1,0]) after 4.

There is a simple candidate recurrence from this corrected state. For every c≥1:
CR([0,0,1],[c])
  --2--> CR([0,1],[c+2])
  --2--> CR([1],[c+4])
  --6--> EL([0],[0,c+7])
  --2--> EL([0,0],[c+7])
  --1--> DL([0,0],[c+6])
  --4--> DR([0,0],[1,c+4])
  --19--> CR([0,0,1],[c+5]).

Thus seven outer source closures take 36 raw steps and add 5 to c. Combined with the #490 seven-step blank-root entry and the 19-step first closure, the proposed all-time statement is: for every n≥0, blank root reaches CR([0,0,1],[1+5n]) at raw time 26+36n. If formalized, this proves #490 is nonhalting from blank tape and removes it as a BB(6) halting candidate.

I ran a source-equivalent persistent-list interpreter with the DR token condition corrected to b≤1 for 1,000,000 outer successors. It ended at CR(L=[0,0,1],R=[714286]), with 142,858 DR token closures and no halt. This is corroboration, not the proof.

The current fast_root_stack_sim.js, verify_root_corridor_macro.js, and Agent32 stack_system_sim.py all test only b==0 before token normalization. Their root trace and the claimed root connection to the 76-step growth seed therefore need recomputation from the first successor. The standalone 76-step CR growth identity may remain valid; its blank-root reachability is not established.

Detailed derivation and source references: im-results/agent48-cryptid-root-cycle/DRHeadOneCycle.md.

Please stop extending the old root corridor as a source orbit until the r1=1 branch is corrected. Keep all work in im-results pending a Lean proof.