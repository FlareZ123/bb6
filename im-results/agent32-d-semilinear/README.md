# No safe semilinear length projection for an infinite Cryptid D orbit

Agent32, 2026-11-24. **Conditional obstruction to a proof class, not a verdict on any root.** The general arithmetic proof is kernel checked; the D specialization below uses established source theorems and a paper identification of the canonical suffix conventions.

## Arithmetic lemma

For H(n,v) denoting eventual halting, suppose every n>=2 is covered by an affine branch n=3k+d_r, d=(3,4,2), and for each suffix v and r the branch either halts uniformly in k or returns to (8k+c,w), c>=2, with w,c independent of k. Suppose also that every suffix has a halting ternary cylinder.

Then every positive arithmetic progression of n>=2 contains a positive-stride subprogression all of whose points halt for v. Proof: induct on the 3-adic valuation of the stride. When the stride is a unit modulo 3, the progression meets the known cylinder by CRT. Otherwise all inputs have the same residue. If that branch is terminal we are done; otherwise its affine image has stride 8d/3, reducing the valuation by one. Pull the inductively obtained subprogression back along the affine map. The same result holds simultaneously for any finite collection of suffixes, by successively refining the subprogression. The empty-suffix cylinder suffices: a B flush branch shortens each nonempty canonical suffix, and backward affine lifting gives a cylinder for that suffix by induction on length.

## Semilinear obstruction

Let P(n,v) be any safe set (every member genuinely nonhalting). For a fixed suffix length m, its unary projection contains no infinite arithmetic progression. Indeed, the 2^m possible suffixes form a finite collection, so any such progression contains a common halting subprogression. At a point in that subprogression every possible length-m suffix halts, contradicting membership in the projection.

Write S={(n,|v|):P(n,v)}. If S is semilinear, express it as a finite union of linear sets b+sum_i k_i g_i with natural coordinate vectors. No generator can have positive first coordinate and zero second coordinate, since this would yield the forbidden arithmetic ray. Thus each generator's first coordinate is bounded by a finite constant times its second coordinate. Taking the maximum of these constants and all base first coordinates yields n<=C(|v|+1) throughout S.

If an infinite trajectory has n_0>=5, 8n_t<=3n_{t+1}+23, and a rank R dominating suffix length with R(v_{t+1})<=R(v_t)+B, then n_t>=5+t and eventually n_{t+1}>=2n_t. Meanwhile |v_t|<=R(v_0)+Bt. The slope bound is impossible. Hence no safe P containing that trajectory has semilinear length projection.

## D application

Use the canonical finite suffix after the unary block and its delimiter, dropping trailing blanks. The total affine recurrence is source-certified in [global-affine completeness](../../results/2026-11-24-d-global-affine-completeness-agent32.md); each branch either terminates or returns with c>=3, independently of k. Observational equality preserves physical halting. For B, remove the delimiter and absorb following ones into the unary block, then canonicalize; each nonempty suffix strictly shortens. The empty suffix has a source-certified halting cylinder from Agent26's DRouteDensity.unary_cylinder_exists (see ../agent26-d-halting-density/), based on the 108-return halting witness. Thus the abstract affine/flush hypotheses hold. The bound 8n<=3n'+23 follows from d_r<=4 and c>=3. Agent3's exact finite rank checker and recurrence in [density-one](../../results/2026-11-24-d-density-one-agent3.md) give per-return canonical rank increase <=11; R(s)=|trim(s)|+2 count_011(trim(s)) dominates the suffix length. Therefore the generic no-go applies to each of the source-connected unary seeds 5,9,15,39, **if its orbit is infinite**.

In particular a context-free safe language of canonical sections cannot contain such an orbit: a finite-state transduction marks the initial unary block separately from the suffix; context-free languages are closed under rational transduction, and Parikh's theorem makes the two lengths semilinear. This is an ordinary mathematical corollary, not a new formalization of Parikh's theorem. It also excludes all safe semilinear length projections regardless of what other data the certificate retains. It does not exclude nonsemilinear or context-sensitive certificates, or decide any individual D trajectory.

## Lean artifact

Decode semilinear.tar.xz.b64 (SHA256 of compressed archive d02a492d894eaa4408552ad94253537c56eb6b44ae97d32ea07483eb6d9ab45b). Lean 4.36.0-rc2, core imports only:
```sh
base64 -d semilinear.tar.xz.b64 | tar -xJ
LEAN_PATH=. lean -o SemilinearNoGo.olean SemilinearNoGo.lean
LEAN_PATH=. lean AffineRayDense.lean
```
Main declarations: finite_dense, no_fiber_ray, safe_semilinear_slope, no_safe_semilinear_orbit, affine_ray_dense, seed_cylinder_of_flush, eventual_doubling, rank_linear, no_semilinear_from_source_bounds. The last theorem's audit is [propext, Classical.choice, Quot.sound]; no sorry. The generic Lean file takes explicit recurrence/rank hypotheses. The D-specific transfer and context-free corollary above are paper arguments using existing source results, not newly imported kernel-checked declarations.

This extends the fixed-modulus invariant obstruction to arbitrary finite-union linear length projections. It is kept in im-results because it is a method limitation, not a root decision or improved BB(6) bound.
