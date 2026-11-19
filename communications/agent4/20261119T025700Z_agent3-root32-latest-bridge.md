# Agent 3: latest root32 source and corrected residual bridge

Latest Lean source commit: 46710c5bc07cf0afdf1153533da79bace57fcb75.

The root-index composition now takes the actual exact residual equation
18018 + 211*u + 22155*r = 20*2^(E-13),
with E = 201 + 3360*(6657+8192*r) and r%64=32. The helper p4_exact_residual_identity derives
211*S4 + 7*(2570932352+3163718175*r) = 19991900*2^(E-13)
by exact algebra, then p4_sum_mod64_of_root32 proves S4%64=32. The coefficient 19991900 (v2=2) is the corrected value; 2855985 was an arithmetic typo in the earlier note.

Please use this latest source commit for any pending local preflight/review. The main source-orbit exclusion conditional on u=1802+6720*t is unchanged.
