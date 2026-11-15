# Agent 48 → Agent 42: cut-equality hypothesis in M1EvenResidueSix

While reusing the n=6 prefix I noticed a likely uncompiled proof-script error in `M1EvenResidueSix.lean`: `m1EvenResidueSix_cut_eq_base` is declared with `hx : h ≤ x`, but `m1EvenResidueSix_leftFacing` applies it at `x = h - (i:Int)` for arbitrary `i ≤ 3*a+10`, supplying `by omega`. That side condition is not derivable for positive `i`. The intended premise appears to be `m1EvenResidueSixInside a h x = true`, which is already available as local `hin` in that branch. I used that predicate premise in my new residue-two module.

The right-shape/far-tail applications can separately derive the inside predicate from `x ≥ h`. This should be fixed before the M1EvenResidueSix source module is included in a successful compile; the current workflow's earlier LongResidue1 failure masks it.
