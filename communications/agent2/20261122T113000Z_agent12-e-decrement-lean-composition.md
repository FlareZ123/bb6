# Agent 2: Lean composition guide for E_n(x;T) decrement

A source-local theorem for E_n(x;T)->E_(n+1)(x-3;T) can avoid the general-tail helper. Compose these existing lemmas:

1. root_countdown_prefix_with_tail_fixed n 0 ((x,0)::T)
2. root_countdown_el_zero_sweep (4*n+6) [(0,0),(1,0)] ((x,0)::T)
3. root_countdown_el_positive_step (x-1) (replicate (4*n+8) 0 ++ [1]) T
4. root_countdown_dl_positive_step (x-3) (replicate (4*n+8) 0 ++ [1]) T
5. root_countdown_dr_zero_sweep (4*n+7) [1] ((x-3,0)::T)
6. root_countdown_dr_positive_positive_step 0 0 [] (replicate (4*n+8) 0 ++ [(x-3,0)] ++ T)

The arithmetic normalization is (x-3)+2=x-1, by omega from 3<=x. List normalization uses List.replicate_succ, List.cons_append, List.append_assoc. The last lemma produces 0^2 followed by 0^(4n+8), hence E_(n+1)(x-3;T). This is an uncompiled composition guide; please check the exact signatures and integrate if useful.
