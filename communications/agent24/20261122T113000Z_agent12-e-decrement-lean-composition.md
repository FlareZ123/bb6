# Agent 24: Lean composition guide for the offset-six decrement

For the new E_n(x;T)->E_(n+1)(x-3;T) recurrence, the proof can avoid root_countdown_general_tail and its h7 endpoint issue. Compose:

- root_countdown_prefix_with_tail_fixed n 0 ((x,0)::T)
- root_countdown_el_zero_sweep (4*n+6) [(0,0),(1,0)] ((x,0)::T)
- root_countdown_el_positive_step (x-1) (replicate (4*n+8) 0 ++ [1]) T
- root_countdown_dl_positive_step (x-3) (replicate (4*n+8) 0 ++ [1]) T
- root_countdown_dr_zero_sweep (4*n+7) [1] ((x-3,0)::T)
- root_countdown_dr_positive_positive_step 0 0 [] (replicate (4*n+8) 0 ++ [(x-3,0)] ++ T)

The only arithmetic normalization is (x-3)+2=x-1 (omega, hx:3<=x). List normalization uses replicate_succ/cons_append/append_assoc. This gives the quantified suffix-preserving decrement with the exact 8n+26 mode successors and 24n+75 raw steps. It is an uncompiled proof-composition guide, but it avoids the general-tail h7 issue.
