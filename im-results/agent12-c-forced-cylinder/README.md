# Computable dyadic lattices for Machine C

## Result and status

The four-sector exact inverse normalizer has a stronger coupled-congruence lift than independent dyadic shifts. For a rejected point (x,y), compute its inverse itinerary signature (P,A). The terminal has signature (1,0); prepend an odd-low/even-seven edge by (P,A) ↦ (4P,4A+1), or an affine/six-even-right edge by (P,A) ↦ (2P,2A). Then every nonnegative shift (x+16u,y+16v) with

    P | v + A(u+2v)

is also rejected. The proof is an induction on x+2y preserving positive shifts and exact divisibility. In weighted-mass coordinates W=u+2v, a two-bit branch sends (W,v) to (W,(W+v)/4), and a one-bit branch sends it to (W,v/2). The divisibility hypothesis implies the next shift has integral coordinates and satisfies the child signature condition. The terminal forbidden parity and sum persist. Thus the old independent rectangle (u,v multiples of P) is contained in the lattice. Since 1+2A is odd and P is a power of two, each u has a unique v modulo P. The index among shifts in units of sixteen is P rather than P².

### A concrete high-stop diagonal family

For the existing source-certified seed (j,m)=(93,6), the high stopping target is (189,1572748). Its signature is (32,10), with three forced steps. The terminal is (1081329,1032169), forbidden because the right coordinate is odd and the sum is 2 mod 4. At all natural t,s,

    j = 93+8t+512s,  m = 6+8t

gives an excluded high stopping target. To see this directly, put q=2^(16t), w=q*(j+3). The right target is 16384w-116-32t-512s, so its shift from 1572748 is 16v with v=1024(w-96)-2t-32s ≥ 0. The left shift is 16u with u=t+64s. Consequently v+10(u+2v)=21504(w-96)-32t-32s, divisible by 32. This sloped family permits m increments of eight, where the previous independent 512-modulus rectangle at this seed requires increments of 512. It provides 64 times the residue coverage of that rectangle in a 512×512 parameter period, with the stated nonnegative orientation.

This compresses rejection certificates of the existing filter; it does not extend the filter itself or prove that all surviving stop parameters are unreachable. No blank-root halt/nonhalt decision follows.

## Files and verification

- ForcedLattice.lean: quantified arithmetic lattice theorem and source-connected corollary.
- HighDiagonal.lean: quantified high-stop diagonal and source-connected corollary.
- ForcedCylinder.lean and ForcedParameterLift.lean: previous independent rectangular theorem and fixed-m / saturated rectangle / low parameter lifts.

The new arithmetic theorems fullForcedExcluded_lattice and high_diagonal compiled locally with Lean 4.36.0-rc2 (b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a), using verbatim arithmetic definitions of the four gates, fullForcedNormalize and fullForcedExcluded from the original modules. Both printed exactly [propext, Classical.choice, Quot.sound]. The committed files import the actual FullForcedFilter, with added source reachability corollaries. Their exact transitive original-source compilation is pending: the local shell has no DNS access to GitHub and no repository checkout. This is arithmetic-model verification only, with the source corollaries stated but not yet compiled. Reuse the existing agent3-c-bounce-inverse.yml forced_cylinder_only target if extending it is necessary. No new workflow or run is required to reproduce the local arithmetic check.

## Earlier rectangular lifts

The preceding theorem used B=16*2^d, where d counts two bits for each odd-low/even-seven edge and one for each affine/six-even-right edge. Every rejected point lifts by independent B multiples in both coordinates. The parameter specializations give fixed-m j progressions and, when the exponential term is divisible by B, high rectangles and low progressions. Those arithmetic results were locally compiled against verbatim definitions; the full source closure was not accepted in that invocation.

## Remaining question

Use the lattice representation to combine rejected families across different base points and derive a source-relevant exclusion of a surviving stop domain. The lattice does not address nonforced inverse branching and must not be mistaken for a solution of Machine C. 
