# Two-coordinate finite exclusion of periodic reset itineraries

**Status (24 November 2026).** Paper reduction of every valid periodic reset itinerary to a finite exact search for its total level increment D. The rational-denominator lemmas in [PeriodBetaDenominator.lean](PeriodBetaDenominator.lean) compile locally under Lean 4.36.0-rc2, with standard axioms only. The full reduction and computational enumeration are not kernel-certified. This excludes every periodic itinerary with 1 <= D <= 80 (prepared or rooted); it does not decide the authentic #746 orbit or exclude unbounded periods.

## Setting and parameter bounds

Use the exact reset recurrence and rigidity from [PeriodicRigidity.md](PeriodicRigidity.md). A nonempty periodic token word has length L, total valuation A=sum a, and total sweep increment D=sum delta>0. Put P=2^(A+L), R=3^A, G=2^D. At each phase the hypothetical infinite integer solution has X=alpha*2^k+beta*k+gamma. Its normalized slope z=alpha/16=n/q is reduced, with n,q odd, gcd(q,6)=1, 1/2<z<1, q>1. The slope recurrence is z'=3^a(z+1)/2^(a+1+delta); q divides PG-R and (G-1)^2.

The strict slope band gives delta<=a (otherwise z'<=(3/2)^a/2^(a+1) <1/2), so D<=A. More directly for delta>=a+1, z'<3^a/2^(2a+1)<=1/2. Multiplying the slope ratios around the word yields
    PG/R = product_i (1+1/z_i),
so 2^L<PG/R<3^L. Consequently 3^A<2^(A+D) and 2^(A+L+D)<3^(A+L). Let M(D) be the largest integer a with 3^a<2^(a+D); then D<=A<=M(D) and L>=max(1,M(D)+1-A).
During each zero-valuation run delta=0 and q-n halves at each step. After m successive zero tokens the positive even gap is still even, hence 2^(m+1) divides the initial gap, which is <q/2. Since q<2^(2D), m<=2D-3. There are at most A positive tokens, so L<=A*(2D-2). D=1 is impossible already by q|(G-1)^2.

## Denominator identity and an independent rational map

At a phase, the integer difference X(k+D)-X(k)=alpha*2^k*(G-1)+beta*D gives
    q/gcd(q,G-1) = r/gcd(r,D),                     (1)
where r is the reduced denominator of y=beta/2 (also of beta). Indeed two rational terms summing to an integer have equal reduced denominators, and multiplying by an integer cancels precisely its gcd with the reduced denominator. This arithmetic is kernel-checked in PeriodBetaDenominator.lean.

Unlike z, y follows a recurrence independent of delta:
    y'=3^a*(y+1)/2^(a+1).
A full word composes to y'=(Ry+U)/P, where U is positive odd by induction, so y=U/(P-R). P-R is odd and nonzero. Each cyclic phase has the same P,R, hence the same sign of y, and an odd reduced numerator and denominator. The denominator divides |P-R| and is coprime to 6 because A>0. It stays constant along the cycle (a step can only reduce the odd denominator, and the cycle returns). Writing y=p/r gives the deterministic integer update
    a=v2(|p+r|)-1,  p'=3^a*(p+r)/2^(a+1).
The sum is nonzero, since a zero successor would contradict the odd numerator. A positive cycle with A>0 has every y>1: the minimum is at least (minimum+1)/2, equality would force every preceding phase and token to be 1 and 0 respectively. Negative cycles have every y<-1 since all successors are negative.

## Small lifted denominators

Set H=(G-1)^2 with factors of 3 removed (it is odd), and for each A,L in the bounds above set
    g=gcd(PG-R,H),   smax=g/gcd(g,G-1).
Discard g=1. Since q|g, q/gcd(q,G-1) divides smax. Equation (1) then bounds
    r | C = gcd(|P-R|, D_6*smax),
where D_6 is D with all factors 2 and 3 removed. The quotient-gcd monotonicity and cap theorem are kernel checked in PeriodBetaDenominator.lean.

At least one phase has |y|<=B, computed without real logarithms. If P>R, use P/R=product(1+1/y_i); take the least integer m>=1 with (m+1)^L*R<=m^L*P and B=m. If P<R, use R/P=product |y_i|/(|y_i|-1), interchange P and R in this inequality and take B=m+1. For L>=2A, P>R and B=2 suffices, because 3^(A+L)<=2^(A+2L). This follows from 27<32 at L=2A and 3<4 for subsequent increments. These bounds ensure some phase is in a finite search interval.

Lift each reduced r to a multiple C by multiplying its odd numerator by C/r, preserving the valuation and integer update. For each signed cap and bound, enumerate odd numerator magnitudes C+2,...,B*C. Follow the deterministic update only until returning to the start, falling below its magnitude, exceeding total valuation M(D), or exceeding length M(D)*(2D-2). Every relevant primitive y-cycle must be found from a minimum-magnitude phase. A larger cap with the same sign and at least the same bound subsumes all divisor caps. Reduce duplicates. The full token word may repeat a primitive y-cycle; test every repetition allowed by the A,L bounds.

## Recover the normalized slope word

For each remaining valuation word and each step, z maps to 3^a(z+1)/2^(a+1+delta), where delta is chosen to place the result in (1/2,1). On that interval there is at most one seam, since the undivided image spans a ratio 4/3<2. The map is injective on its valid domain: if two outputs coincide, the two inputs plus 1 have ratio a power of two, necessarily 1. Therefore the composition of L such maps has at most L+1 affine pieces (each new seam has at most one preimage). On each piece solve the affine fixed-point equation exactly, enforce strict bands, total D, q>1 and gcd(q,6)=1, q|H, and (1). Reduce the resulting word to its primitive period and reapply the denominator tests for that period. All tests are rational/integer and finite. Every genuinely infinite periodic word must survive; a surviving word would still require the sufficient all-time prepared certificate of [PresburgerPeriodicity.md](PresburgerPeriodicity.md).

## Reproduction and result

Run `python3 period_beta_search.py 80`. Local runs for D=1..40 and 41..80 returned zero survivors, with aggregate 3,298,081 nontrivial-gcd parameter pairs, 649 lifted caps, 701,611 beta starts, 2,476 beta-cycle records, 2,080 slope words, 147 slope fixed points. This is a computational exclusion using the paper completeness argument, not an unbounded proof. The former slope-graph scan D<=14 is superseded in range. Lean: `lean PeriodBetaDenominator.lean` (4.36.0-rc2); all printed axioms are among propext, Classical.choice, Quot.sound.

## Consequence for binary-valuation periodic words

If a is always 0 or 1, the strict slope band forces delta=a. A mixed valuation word has 1<y<3 at every phase: the two contracting maps y->(y+1)/2 and y->3(y+1)/4 preserve [1,3], and a mixed composition sends both endpoints strictly into it. The primitive y-cycle and primitive token word have equal lengths, since the deterministic y recurrence determines a and delta=a. Thus L<=r-1 (odd numerator p strictly between r and 3r), D<=L<r. If q divides G-1, (1) forces r|D, contradiction. Every such periodic word must have q not dividing G-1; in particular q cannot be squarefree, as q|(G-1)^2. Pure a=1 has primitive period (1,1), excluded by D=1; pure a=0 has D=0. This is an all-parameter necessary obstruction, not an exclusion of every mixed binary-valuation word.

## Remaining problem

No finite-D cutoff follows from these arguments. The authentic orbit may be nonperiodic and the exact fatal-index frontier is unchanged. Future effort should prioritize an unbounded or rooted certificate, rather than extrapolating this finite scan.
