# Four-hole extension of Raw13 #1093

The exact table is `1RB1LD1RC---1LA1RE1LF0LA---0RD------`. The F0=1LC branch is the already accepted conditional three-hole theorem at 134, not re-enumerated. On the other branches a candidate scan found 62 difficult one-hole leaves. An extended simulation finds one actual first halt query at time **62122** (62123 including the halt transition):

`1RB1LD_1RC0RB_1LA1RE_1LF0LA_1LA0RD_1LE---`.

All six zero rows write 1; its incoming zero-write delay is exactly zero. The previous 629 finite maximum was not a valid bound. The 61 other difficult leaves survive two million ordinary transitions in direct simulation, but this is not a nonhalting proof.

The new generator uses the established FAR/sweep witnesses, exact subtree grafts, and chunked zipper certificates for late halts. The intended bound for the resolved portion is 62123 with an explicit residual complement. No unconditional four-hole bound is claimed until kernel checking and closure of all residuals.
