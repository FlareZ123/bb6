# Exact prepared ancestry and rooted endpoint equivalence

The four-digit signed path reduction has an exact converse **for prepared states of the original accelerator**, including all actual branch guards. This does not infer blank reachability from signed path existence.

Write (m=8u+5), (n=23+32u=4m+3), and suppose the q0 target satisfies
`a+24u+19=13*2^n`, `b+13=2*a`. Use shifted coordinates `a=4*x-3`, `2*a+b=4*r-1`. Let a signed path start at `p=24u+22`, `y=6u+4`, have length m, end at (P,Y), and have little-endian digit polynomial `D=sum(d_i*16^i)`.

Then its reconstructed endpoint is uniquely specified by
```
R + P = 104 * 16^m
X + Y = 26 + 104 * D
original(X,R) = (4*X-3, (4*R-1)-2*(4*X-3))
```
with X≥25 and 3X≤R. Running exactly 4m original accelerator steps from this endpoint returns the q0 target. With the existing Source Rooted interface, the target is blank-reachable **if and only if** such a signed path exists whose reconstructed endpoint is itself blank-reachable.

## Proof

The three non-special inverse equations F, S and E, expressed in first coordinate and total rank, suffice for the exact deterministic next-step equality. The Lean proof checks the inequalities selecting each branch, the natural subtraction bounds, parity, and exclusions of the exceptional S/E cases. Each of the four digit equations `r=R+cost(d)`, `16*X+offset(d)=x+d*r` therefore gives a genuine four-step chain in the cone x≥400 and 3x≤r. It also preserves the cone backwards and gives x≤16X.

For the signed step `16*y'=y+d*p+offset(d)`, the leading factors in `r+p=16^m*A`, `x+y=16^m*B` cancel the offset exactly. Set `R=r-cost(d)` and `X=16^(m-1)*(B+d*A)-y'`. The cone makes both subtractions legitimate. The new invariants have leading coefficients 16A and B+dA, respectively. Induction gives the endpoint formula and concatenates the real run. Conversely, the existing Source necessity proof retains the root predicate at every endpoint. Rooted endpoint equality is sufficient by run_add.

Since the digit costs range from 3 to 6, P lies between 48u+37 and 72u+52. Thus any genuine endpoint lies in an explicit rank window of width 12m in the original accelerator around 416*16^m. This is a potentially useful target for a separate global blank-orbit analysis. The signed path constraints alone do not show that this window lacks rooted endpoints.

## Formal status

`Q0Converse.lean` was compiled with Lean 4.36.0-rc2, importing the exact repository Q0MacroCore and BB429Rank (blob 5a93ba2d833ca375478f1183f45712a34f299f19). Exported theorem axiom checks for macro_converse, path_end_lift, q0_prepared_ancestry, rooted_path_end and q0_rooted_iff_endpoint report only propext, Classical.choice, Quot.sound. No sorry, native_decide, or unproved branch guard. The iff retains Source Rooted as an explicit argument; the prior Q0MacroSource adapter provides the definitionally corresponding source interface, but was not recompiled in this checkpoint. No q0 all-parameter exclusion, machine #429 decision, or BB(6) value is claimed.
