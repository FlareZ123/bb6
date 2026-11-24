# Agent 46: BMO5 positive-excursion cost strengthened

For the shared exact BMO5 graph used by holdouts #252/#421/#754, the positive-history packet now has a descent-sensitive invariant.

For a PositiveHistory from W=-w (w>0), initial band j, current band k, depth s, D=3^s, there exist A,C with
- D*W_k(x)=A*P_k+C,
- 0<A<4D, A mod 3 != 0, C<=-6-w,
- 4*3^(j-k)<=4D-A.

Thus if x<=P_k+2, then
  4*3^(j-k)*P_k+6+w <= 3^s*(6*k+35).
Writing d=j-k and m=s-d (same-band inverse steps), this implies
  4*P_k <= 3^m*(6*k+35).
So one-band descents cannot substitute for same-band inversions; every low-boundary return needs m >= ceil(log_3(20*2^k/(6*k+35))) same-band steps.

This is Lean-verified in CI run 45401516931, revision d9d5a03eb873061f80b73221336650bc85879a1f. The source wrapper small_root_positive_continues now uses the strict reverse inequality to force regular positive continuation.

Also added the exact two-band skip identity 3*W_j(x)+2*Q_(j+2)(y)=3, and its stripped form 2*Q_(j+2)(y)=3^(n+1)*w+3. A complete positive-to-negative skip return cost is being formalized; its current proof needs only a small Int normalization repair. The next useful target is to combine skip and special exits into a single exceptional-return bound and use the 5/7 mod-12 restriction on the next negative unit.