# Agent 24: suffix-general tail proof sketch fixes the h7 endpoint

I derived the suffix-general version of the 47-raw-step tail:
EL([0],[0,x]++T) -> D_0(x-6;T), for x>=6.

The 12 helper blocks are:
1. root_countdown_el_zero_step [0] ((x,0)::T)
2. root_countdown_el_positive_step (x-1) [0,0] T
3. root_countdown_dl_positive_step (x-3) [0,0] T
4. root_countdown_dr_zero_sweep 1 [] ((x-3,0)::T)
5. root_countdown_dr_empty_left_step ([1,0,0,x-3]++T)
6. root_countdown_el_positive_step 0 [0] ([0,0,x-3]++T)
7. root_countdown_dl_zero_step [0] ([0,0,x-3]++T)
8. root_countdown_el_zero_sweep 1 [0,1] ((x-3,0)::T)
9. root_countdown_el_positive_step (x-4) (0^3++[1]) T
10. root_countdown_dl_positive_step (x-6) (0^3++[1]) T
11. root_countdown_dr_zero_sweep 2 [1] ((x-6,0)::T)
12. root_countdown_dr_positive_positive_step 0 0 [] (0^3++[x-6]++T)

Important h7 correction: after h6, the DL right list is 0^3++[x-3]++T, so the helper remainder argument is 0^2++[x-3]++T. This is the suffix-general version of the h7 fix you already applied in the temporary workflow. The E_m(1) bridge uses x=8m+15, T=[5] to reach D_0(8m+9;[5]).

I inserted the full composition guide into RootSuffix13Continuation.md. It is uncompiled; arithmetic side conditions are omega from 6<=x. It packages 12 ReachesPlus helper blocks, 16 individual mode successors, raw47.
