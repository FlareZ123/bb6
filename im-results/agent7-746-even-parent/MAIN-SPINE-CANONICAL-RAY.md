# The even-predecessor spine is the canonical 3-adic ray

**Status: exact algebraic bridge. This is the key interface between the evenPre(n) reverse cone and Agent 10's all-precision ray selectors; it does not yet close the side branches.**

## 1. Spine recurrence

Fix a fatal index n in a surviving sector `n mod 6 ∈ {4,5}` and put

`y₀ = evenPre(n) = 4·2^n − 3n − 7`.

The unique same-scale even ResetParent of a spine state y_m is

`y_(m+1) = 2y_m − 8·2^(n−1) − (n−1)`.

Writing `y_m=4·2^n−D_m` gives

`D₀=3n+7`,
`D_(m+1)=2D_m+n−1`,
`D_m=(4n+6)·2^m−n+1`.

The spine is present while `3 ≤ D_m ≤ 2^n+1`, exactly the scale-(n−1) even image band.

## 2. Exact canonical-ray identity

Agent 10's signed canonical-ray numerator is defined in `im-results/agent7-fatal-density/SignedRayPeriod.lean` by

`signedZ(n,j) = 8·2^n + 2n + 3 − 2^(j+1)(2n+3)`.

Substitute the closed form for D_m:

```text
2y_m+5
 = 8·2^n − 2((4n+6)·2^m−n+1) + 5
 = 8·2^n − (8n+12)·2^m + 2n + 3
 = 8·2^n + 2n + 3 − 2^(m+2)(2n+3)
 = signedZ(n,m+1).
```

Thus, whenever y_m is in the nonnegative spine, it is exactly the canonical ray state at depth `j=m+1`:

`2*y_m+5 = signedZ(n,j)`, with `j=m+1`.

This is an identity for every n,m at the signed-integer level; the spine-band condition supplies the nonnegative Nat interpretation.

## 3. Direct consequences of existing Hensel theorems

Agent 10's `CascadeRayDepthResidue.signedZ_mod_three_even_iff` gives, for every `n mod 6 ∈ {4,5}`,

`3 | signedZ(n,j) ↔ j mod 2 = 0`.

On the even spine `j=m+1`, so:

- if m is even, `2y_m+5` is not divisible by 3 and there is no odd ResetParent at all;
- if m is odd, `2y_m+5` is divisible by 3 and odd-parent branches become possible.

More strongly, `depthResidue_iff` gives the exact all-precision classification

`3^(k+1) | (2y_m+5) ↔ (m+1) mod (2·3^k) = depthResidue(n,k)`.

Therefore the first-tier odd-parent exponents along the entire main spine are governed by one recursively defined 3-adic depth class at each precision. This is an exact theorem for all n in the two surviving sectors, not a finite residue sample. For the complete n=887 finite-depth evaluation, including the exact t=1,3,6 band-valid branch classes and the 17 second-tier fork depths, see [N887-MAIN-SPINE-BRANCHES.md](N887-MAIN-SPINE-BRANCHES.md).

## 4. Second-tier and nested branches

For the t=1 odd-parent branch, Agent 10's `TWO-TIER-INDEX-HENSEL.md` identifies the correct second-tier numerator

`T_n(j)=16·signedZ(n,j)−9(12·2^n+6n+3)`.

Under the stated t=1 source-band hypotheses, if w is the actual even ResetParent of the actual odd predecessor, then

`T_n(j)=9(2w+5)`.

The depth-coordinate selector in `RayTwoTierDepthHensel.lean` therefore classifies the next odd-parent gate on the same spine. Agent 10's n=887 diagnostic finds the high-valuation second-tier depths `j=6,168,330,492,654,816` (with the exact valuations recorded in `TWO-TIER-DEPTH-887-RESIDUES.md`).

For higher odd exponents t, the nested numerator is

`W_(j,t)(n)=2^(t+1)·signedZ(n,j)+5·3^(t+1)`.

Agent 10's `nestedOddIndexResidue` selector is intended to classify these nested 3-adic gates at every precision. The remaining proof obligations are the exact dyadic-band tests for each candidate t and the recursive source-parent classification after the corresponding odd parent is formed.

## 5. Research consequence

The finite n=887 cone is not an arbitrary 1,319-entry accident. Its main spine is a canonical ray whose odd-parent opportunities have a complete Hensel description. The natural proof strategy is now:

1. parameterize the main even spine by `j=m+1`;
2. use `depthResidue` to enumerate every first-tier odd-parent valuation on that spine;
3. apply the second-tier selector to the actual t=1 branches and the nested selector to higher t;
4. discharge the dyadic-band inequalities exactly, including the high-valuation exceptional depths;
5. show every generated side branch terminates in a parent-free gap, uniformly in n in the relevant residue class.

This replaces a finite reverse-cone list with a symbolic branch grammar. It is the most promising route identified here for proving evenPre(n) unreachable on an infinite family.

## 6. Scope and caveats

- The identity `2y_m+5=signedZ(n,m+1)` is exact algebra.
- The depth Hensel selectors are existing Lean drafts in the repository; their current CI status must be checked before citing them as verified.
- The second-tier identity is conditional on the specific source-band hypotheses in Agent 10's note.
- The finite cone census in `FIVE-LIFT-EVEN-PRE-CONE-CENSUS.md` is exact-integer computation, not a family proof.
- No blank-root exclusion for the whole infinite evenPre family, and no BB(6) solution, is established by this note.

— Agent 7
