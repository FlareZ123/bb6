# Dual 3-adic Hensel coordinates on the #746 fatal inverse ray

**Status (12 November 2026):** the arithmetic statements and Lean proof drafts are committed. The new source has been added to the existing manual source-check workflow, but no successful CI run exists for this revision. This is intermediate research, not a blank-root exclusion or a BB(6) solution.

## 1. Signed canonical-ray numerator

Write

~~~text
Z_j(n) = signedZ(n,j)
       = 8*2^n - 2*(2^(j+1)-1)*n + 3*(1-2^(j+1)).
~~~

The existing depth-coordinate Hensel theorem fixes n and selects the unique depth residue modulo 2*3^k at which 3^(k+1) divides Z_j(n).

## 2. Complementary index-coordinate selector

For either surviving fatal sector s in {4,5} and every even depth j, there is a unique residue R(s,j,k) modulo 3^k such that

~~~text
3^(k+1) | Z_j(s+6*h)
    iff h mod 3^k = R(s,j,k).
~~~

The recursive selector is indexResidue. The exact shift uses D=2*3^(k+1)=6*3^k and the depth-period identity

~~~text
2^D = 1 + 3^(k+2)*depthCoeff(k+1).
~~~

For a_j=2^(j+1)-1, the signed numerator changes by

~~~text
Z_j(n+D) = Z_j(n) - 4*a_j*3^(k+1)
                    + 8*2^n*depthCoeff(k+1)*3^(k+2).
~~~

Since a_j is 1 modulo 3 for even j, exactly one of the three index digits lifts divisibility from 3^(k+1) to 3^(k+2).

The Lean theorems depth_index_duality and indexResidue_bijective show that the depth and index selectors are inverse coordinates of the same 3-adic congruence surface. In each precision block, the even depth classes in one full depth period are in bijection with the fatal-index classes.

For the first packet (k=1):
- Sector s=4: depths j=0,2,4 correspond to index digits 0,2,1.
- Sector s=5: depths j=0,2,4 correspond to index digits 0,1,2.

## 3. Nested odd-parent numerator at arbitrary even depth

If an odd parent of the ray node has the form x=2^t*d with 3^(t+1)*d=Z_j(n), then its next odd-parent numerator is

~~~text
2*x+5 = W_(j,t)(n)/3^(t+1),
W_(j,t)(n) = 2^(t+1)*Z_j(n) + 5*3^(t+1).
~~~

For s in {4,5} and even j, W_(j,t)(s+6*h) is divisible by 3 for every h,t. Its exact three-digit shift is

~~~text
W_(j,t)(n+r*D)
  = W_(j,t)(n)
    - 3^(k+1)*2^(t+3)*(2^(j+1)-1)*r
    + 3^(k+2)*C,
~~~

for r in {0,1,2}, with an integer correction C. The coefficient 2^(t+3)*(2^(j+1)-1) is a 3-adic unit for even j.

The Lean draft proves:
- nestedOddNumerator_sector_mod_three: the base divisibility by 3;
- nestedOddNumerator_lift_criterion: the exact one-digit divisibility criterion;
- nestedOddNumerator_unique_lift: precisely one of the three next digits lifts;
- nestedOddIndexResidue and nestedOddIndexResidue_iff: the full recursive selector, proving that for every precision k the admissible fatal indices form exactly one residue class modulo 3^k.

This is the index-coordinate complement to translated high-gate Hensel selectors, which fix the fatal index and solve for a depth class. The full nested selector is now implemented; it is not merely a finite diagnostic.

## 4. The t=3 second-parent split

For the t=3 high-q gate, put e=W_(j,3)(n)/3^8. Since

~~~text
2^6*(2^(j+1)-1) = 1 (mod 3)
~~~

for even j, the next nested index Hensel digit d is exactly e modulo 3. This is formalized by tThreeHighGate_digit_eq_quotient_mod_three.

The source equation for the second t=3 parent's target index,

~~~text
16*e = 8*2^(n-6) + r + (n-6) + 5,
~~~

and n modulo 6 in {4,5} imply r=e+1 modulo 3. This is formalized by tThreeSecondParent_index_relation. Therefore

~~~text
r = d+1 (mod 3).
~~~

The already-excluded r=0 branch corresponds to d=2. The remaining r=1,2 branches correspond to d=0,1 respectively. This separates the parent height 8*e from the next target index r and gives a precise index-digit parameterization of the two unresolved branches.

## 5. BB(6) relevance and strict boundary

An odd inverse parent at ray node Z_j(n) requires the appropriate 3-adic divisibility, as well as the dyadic source-band condition. These selectors locate the fatal-sector indices at which a fixed even-depth node can have the required valuation and identify the unique depth class for a fixed fatal index.

They do **not** establish the dyadic source band, do not prove that any such odd parent is reachable from the blank root, and do not exclude the even fatal predecessor. The next research step is to combine the t=3 index-digit classification with the root-sensitive parent analysis for r=1,2. Keep these results in im-results until the Lean source check and adversarial review succeed.
