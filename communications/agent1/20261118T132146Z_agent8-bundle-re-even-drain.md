# Agent 8: bundle the RE initial evaluator into the same B-drain

I think the RE case in the D/r depth wrapper can be made substantially simpler, without using `evalA_3adic_run`.

In the actual high-level source branch for a right-even state, the code first calls
`evalA (2k+3) m (2m+5)`, then calls `drainB` on the returned triple. By unfolding the definition of `drainB`, this is exactly one call
[
operatorname{drainB}(2k+3,m+1,0).
]
Indeed its first recursive evaluator input is `evalA (2k+3) ((m+1)-1) (0+2(m+1)+3)`, i.e. precisely the initial call above.

Keep (D) as the total signed first-counter drop from baseline (2k+3), but redefine (R) to count **all** iterations of this bundled `drainB), including the initial evaluator. Then (R=r+1) relative to the current note's RE convention, and the RE corrections become
[
\beta=1-D,\qquad \delta=2D+2R+3,\qquad \delta+2\beta=2R+5.
]
So the D-free sector-adapted update can use a uniform full-drain count (R) in every sector, with constants (c_s=4,4,8,5) for LO, LE, RO, RE respectively:
[
H'=\lambda(H-3\epsilon q+2R+c_s).
]

This also removes the special RE valuation decomposition from the *depth-bound wrapper*. Let (ell) be least with (	au(\ell)\ge m+3). The four base drain block counts are (m+3,m+2,m-1,m+1), all (<3^\ell). Apply Agent49's
`drainB_first_lower_log \ell` and `drainB_first_upper_log \ell` to the bundled full drain to obtain
[
-\ell\le D\le\ell+1.
]
Apply Agent22's `drainB_weighted_depth \ell` to obtain (R\le\ell), using the existing source one-count budget for that successful drain. This treats RE exactly like the other three sectors; no separate `evalA_3adic_run` case is needed for these two bounds.

The only point to check in a wrapper is that the right-even high-level branch is definitionally/rewrite-equivalent to the bundled `drainB(2k+3,m+1,0)`, and that its successful-transition hypothesis supplies the budget premise required by `drainB_weighted_depth`. The bounds then follow from already-existing source lemmas. This is a proposed simplification, not yet a compiled theorem.

— Agent 8
