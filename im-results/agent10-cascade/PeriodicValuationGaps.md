# Collatz coordinate and ordered slope gaps

**Status (24 November 2026):** New paper theorems over the exact reset arithmetic and periodic rigidity. Every periodic itinerary of constant valuation is impossible, with no bound on valuation or period length. More generally, the primitive valuation cycle constrains the repetition factor of a full token period; for a primitive valuation word of length two, the factor is at most seven. The core integer identities are locally kernel-checked in [PeriodCollatz.lean](PeriodCollatz.lean) and [PeriodSlopeGap.lean](PeriodSlopeGap.lean), Lean 4.36.0-rc2. The cyclic-order argument is a paper proof, not an original-machine Lean certification. No authentic root decision follows.

## 1. Exact Collatz interpretation of the second coordinate

Use [PeriodicBetaSearch.md](PeriodicBetaSearch.md), with y=beta/2=p/r in lowest terms and slope z=n/q in (1/2,1). The common odd denominator r of y is fixed on a cycle. Its deterministic update is p'=3^a*m, p+r=2^(a+1)*m, m odd.

Set x=(y-1)/2, with numerator N=(p-r)/2 and denominator r. Thus N+r=2^a*m. The usual shortcut Collatz map on rationals of odd denominator r is, on numerators,
    T_r(N) = N/2 if N even; (3N+r)/2 if N odd.
For j=0,...,a, the numerator after j initial odd steps is 3^j*2^(a-j)*m-r. It is odd for j<a and even for j=a. One final even step gives (3^a*m-r)/2=(p'-r)/2. This is precisely the next second-coordinate state. The proof also works for signed numerators. PeriodCollatz.lean proves this block identity for arbitrary integer odd r,m and natural a.

Consequently a primitive second-coordinate cycle of length m with valuation word a_0,...,a_(m-1) is exactly a rational Collatz cycle grouped as runs of a_i odd steps, each followed by one even step. Conversely any rational Collatz cycle with at least one even step yields such a second-coordinate cycle. A primitive grouped cycle corresponds to a primitive Collatz cycle (group boundaries are exactly the states immediately after an even step). This relates periodic reset exclusion to the established rational Collatz cycle problem, without claiming a solution of either problem. Background: J. C. Lagarias, *The set of rational cycles for the 3x+1 problem*, Acta Arith. 56 (1990), 33–53; Bell and Lagarias, [rational cycles and integer 3x+k dynamics](https://www.impan.pl/shop/publication/transaction/download/product/82190).

In particular, if r=1, the only already familiar integer cycles cannot support a reset period: x=0 implies A=0; x in {1,2} gives constant a=1; x=-1 has no even step; x in {-5,-7,-10} gives constant a=2; and the negative cycle of -17 gives a grouped word (4,3,0,0) up to rotation. For the -17 cycle, the two trailing zero tokens force the next slope above 7/8, hence the a=4 token has delta=3 (the seam is at 47/81); a=3 always has delta=2. The two zero tokens have delta=0. Thus the block map is one affine contraction and all periodic slopes are fixed under the block; its unique fixed point at the a=4 phase is 58251/63349. Since D=5 and 63349 does not divide 961, this cycle also cannot support a reset period. No classification of all integer Collatz cycles is assumed here.

## 2. Ordered slope gaps: general theorem

Suppose a hypothetical periodic itinerary has primitive full token length L=m*b, where m is the primitive valuation-word length (equivalently the primitive y-cycle length), and b is its repetition factor. Let A=sum a, D=sum delta>0, Q=2^(A+L+D)-3^A. All normalized slopes have the same reduced odd denominator q dividing Q and (2^D-1)^2.

At each valuation phase j modulo m, sort the b distinct slope states as
    1/2 < z_0 < ... < z_(b-1) < 1.
The states are distinct: if the same slope recurs at the same valuation phase, the deterministic normalization chooses the same delta and all future tokens repeat, contradicting primitive full token length.

The step at phase j maps z to 3^a(z+1)/2^(a+1+delta), choosing the unique delta that keeps the image in (1/2,1). Over the finite phase set, the undivided values span ratio less than 4/3, so delta is either constant d or takes two consecutive values d,d+1. Put c=3^a/2^(a+1+d). If both values occur, the lower slopes take the factor c and the higher slopes c/2. All images from the upper group are below every image from the lower group because (z_high+1)/(z_low+1)<2. Thus the map preserves cyclic order, with a single rotation of the sorted indices. With constant delta it preserves ordinary order.

For each phase define the b positive circular gaps
    g_i=z_(i+1)-z_i          (0<=i<b-1),
    g_(b-1)=2*z_0-z_(b-1).
Every gap is strictly between 0 and 1 and has an integer numerator over q. Associate each gap with its lower endpoint in cyclic order (the last gap is associated with z_(b-1)). The following four cases are exact:

* Ordinary interior gap with both endpoints using the same multiplier: g'=c*g or (c/2)*g.
* Interior gap straddling the normalization seam: its image is the circular boundary gap, and g'=c*g, since the doubled smaller image cancels the extra division by two.
* Circular boundary gap, with both multiplier groups present: the images are ordinary adjacent points, and g'=(c/2)*(g+1).
* Circular boundary gap, with one multiplier group: the image is another circular boundary gap, and g'=c*(g+1).

Hence in every case the gap uses the multiplier of its associated endpoint, and gets an additive +1 inside the multiplier exactly at a circular boundary gap. This remains true for b=1, with its unique gap defined as z_0.

The gap transitions follow the same cyclic permutation as the endpoint transitions, so they form a single cycle of length L. There are exactly m additive events, one at each valuation phase. Split the cycle at these events. Let segment i consume total binary exponent B_i=sum(a+1+delta) and ternary exponent A_i=sum a. Its start and end gap numerators N_i,N_(i+1) satisfy
    2^B_i * N_(i+1) = 3^A_i * (N_i+q),    0<N_i<q.
Since 2 and 3 are coprime, 2^B_i divides N_i+q, so 2^B_i<2q. This is kernel-checked in PeriodSlopeGap.lean. Multiplication over the m segments yields
    2^(A+L+D) < (2q)^m.                   (1)
The first-difference identity gives q<=r*(2^D-1)<r*2^D, hence
    2^(A+L+D) < 2^(mD)*(2r)^m.             (2)
The gap cycle also has an affine fixed point with numerator a sum of only m monomials in powers of 2 and 3, and full unsimplified denominator Q. Each additive event contributes exactly one term, and all other gap steps only rescale. This is a structural sparsification: the slope equation ordinarily has L additive terms, whereas the gap equation has m.

## 3. All constant-valuation periods are impossible

Here m=1, A=aL. There is exactly one additive gap event. If L=1, the gap is the slope itself and the numerator of its affine fixed point is 3^a. For any L, composing the gap transitions from the unique boundary event gives
    Q*N = 3^A*q
for the gap numerator N at that event. Since Q is odd and coprime to 3 (A>0), Q divides q. Equivalently, a phase immediately after the event has a monomial numerator over Q, coprime to Q. The explicit two-endpoint identity with the ordinary gap chain is also proved by constant_gap_denominator in PeriodSlopeGap.lean.

Since q divides Q, necessarily q=Q. But slope rigidity yields D<=A and 3^A<2^(A+D), so
    Q=2^(A+L+D)-3^A > (2^L-1)*2^(A+D) >= 2^(2D) > (2^D-1)^2,
contradicting q|(2^D-1)^2. The final arithmetic exclusion is kernel-checked. Therefore no infinite periodic successful reset itinerary can have a constant valuation, including arbitrarily large a and arbitrarily varying sweep increments.

This improves the previous single-positive-token exclusion in a different direction: that theorem allowed arbitrary numbers of zero tokens, while this theorem handles all-constant positive valuations with arbitrarily long nonconstant increment words.

## 4. Primitive valuation length two: repetition factor at most seven

Let m=2, A=b*A0 and L=2*b. The reduced second-coordinate denominator r divides |2^(A0+2)-3^A0|, by the two-token composition. In particular
    r < max(2^(A0+2),3^A0).
Equation (2) gives
    2^(A+L-D) < 4*r^2.
On the other hand the slope product gives 2^(A+L+D)<3^(A+L), whence D<(3/5)*(A+L), using (3/2)^5<2^3. Thus A+L-D>(2/5)*b*(A0+2).
If b>=8, the lower exponent exceeds (16/5)*(A0+2). But
    log2(4*r^2) < 2+max(2*(A0+2),(16/5)*A0),
using 3^5<2^8. Both terms on the right are strictly smaller than (16/5)*(A0+2) for A0>=1. Contradiction. Hence b<=7 and the full period contains at most 14 reset tokens, regardless of the two valuation magnitudes.

For general m, inequality (2) remains valid but does not yield a uniform repetition bound when D is large compared with A+L. No general periodic exclusion is claimed.

## 5. A large conditional exclusion for positive integral Collatz coordinates

For r=1 and y>0, the associated Collatz cycle is a cycle of positive integers (y=1 and x=0 would force A=0). The trivial positive cycle has constant a=1, already excluded. Use the published computational result of D. Barina, [Improved verification limit for the convergence of the Collatz conjecture](https://doi.org/10.1007/s11227-025-07337-0), Journal of Supercomputing 81 (2025), that every positive integer below N=2^71 reaches 1. Consequently every member of a nontrivial positive integer cycle is >=N. If A0 is its primitive odd-step count and P0 its primitive total shortcut-step count, multiplication of the ratios along the cycle gives
    0 < P0/A0-log2(3) <= log2(1+1/(3N)) < 1/(3N ln(2)) < 2^(-72).
Here ln(2)>2/3 follows from its atanh series.

Exact rational bounds enclosing this interval are
    103768467013/65470613321 < log2(3),
    log2(3)+2^(-72) < 10439860591/6586818670.
They are Farey neighbors (cross determinant 1). For a fraction P0/A0 strictly between them, its denominator is at least 65470613321+6586818670=72057431991. The exact rational inequalities are kernel-checked in [PeriodCollatzBound.lean](PeriodCollatzBound.lean) using 64 terms of the atanh series for ln(t), with x=(t-1)/(t+1), and upper tail 2*x^129/(129*(1-x^2)). The Farey denominator theorem is also kernel-checked. The analytic series estimates and Barina's external computation are explicit dependencies, not Lean axioms silently introduced into the proof.

The full reset word has A>=A0. By the strict slope product, D>A*(log2(3)-1), so D>(103768467013-65470613321)*A/65470613321. The kernel-checked integer calculation gives D>=42150895613. Thus all hypothetical periods with positive integral y are excluded through D=42,150,895,612, independently of the general D<=80 computation. This bound is conditional on the cited published Collatz verification and does not cover fractional y or negative integer cycles other than the familiar ones above.

## 6. Scope and next mathematical step

The new all-constant exclusion is independent of the D<=80 computation. The primitive two-valuation result reduces that family to a bounded number of reset tokens, but does not yet bound the valuation magnitudes or decide it. A promising next step is to combine the sparse gap numerator with modular constraints on q and r for fixed small m, or use the Collatz correspondence to transfer independently established cycle exclusions. The authentic blank-reset orbit need not be periodic; the original-source cutoff and global BB(6) decision status are unchanged.
