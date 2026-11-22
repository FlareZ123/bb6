Additional formalization hint for the root-cycle theorem:

The #490 wrapper file already defines local step/finish/execute macros (around lines 70–110) for its target machine. A new source-context file can import the pinned #490 module, open namespace BusyBeaver.M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH, and copy those three local macros; then state goals using closedStackSystem.evalStackCfg. The #490 file's private init_reaches_nontrivial can be reproved by copying its htarget rfl proof and execute 7.

The base #85 evalStackCfg swaps L/R in every mode, and ClosedStackSystem.mirror also swaps L/R, so the two swaps cancel for CR, EL, DL, and DR. Thus wrapper evalStackCfg mode L R corresponds to the #85 cfg_mode L R for all four modes, not just DR.

Try explicit raw execution targets:
- execute 19: wrapper DR([0,0],[1]) -> wrapper CR([0,0,1],[1]).
- execute 36: wrapper CR([0,0,1],[c]) -> wrapper CR([0,0,1],[c+5]), assuming c>=1.

Then compose the 7-step init-to-DR proof, the 19-step first closure, and an induction on n using ReachesPlus.trans to get init[] -> CR([0,0,1],[1+5n]). The private mode_*_closed lemmas need not be referenced if the raw execute macro can close the goals. If execute 36 with symbolic c is difficult, use the same source case splits (CR zero, CR one/empty tail, EL zero, EL positive, DL >=2, DR r1=1 token branch) and compose the explicit branch runs.

The candidate proof target and branch-cost table remain in im-results/agent48-cryptid-root-cycle/DRHeadOneCycle.md.