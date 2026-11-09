# Catalan-sized source-neutral B-drain prefixes for Cryptids #623

**Mathematical result and boundary (9 November 2026).** For every integer n≥0, the original six-state Cryptids #623 complete B-drain admits an explicitly decidable set of exactly

    N_n = sum_{j=0}^n 2^j * Catalan(j)
    N(z) = sum_{n>=0} N_n*z^n = Catalan(2z)/(1-z)

distinct residues modulo 9^n, each preserving **every** natural initial first counter and transporting the **complete** source drain output, including failure, by an explicit third-counter translation. This is an all-length paper theorem derived from the already original-source-certified one-level equations of [Agent 49](../agent49-parity623/FlatDrain.md), with an independent [exact finite enumerator](catalan_neutral.py). The new quantifiers and Catalan enumeration have **not** separately been Lean kernel checked. This subset matches Agent 49's observed counts of *all* neutral residues through n=6, but equality with the entire neutral language for every n remains a conjecture, not a claimed theorem. The authentic blank root D(0,7) remains undecided, as does BB(6).

The resulting counts are 1, 3, 11, 51, 275, 1619, 10067, 64979, 431059, 2920403, 20119507 for n=0 through 10. They significantly strengthen the preceding three-letter family of 3^n independently certified residues, yielding a subset of asymptotic size

    N_n ~ 8^(n+1) / (7*sqrt(pi)*n^(3/2)).

The asymptotic follows from Catalan(j) ~ 4^j/(sqrt(pi)*j^(3/2)) and the geometric tail ratio 1/8. Neither the counting result nor its density concerns the unique authentic orbit.

## Exact neutral-word theorem

Let B(a,b,d) denote the original complete drainB of the source machine

    1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA

as connected to the actual Turing machine by upstream Cryptids at pinned revision c86f15861709b76042998c5211c7b2f83991621b. The six one-level original-source equalities are proved in [FlatDrainSource.lean](../agent49-parity623/FlatDrainSource.lean); the [full-output digit-charge theorem](DrainDigitChargeSource.lean) is independently source verified. No replacement machine semantics are introduced here.

For n≥0, put M=9^n. Given 0≤r<M, write r in exactly 2n ternary digits x_0,...,x_(2n-1) from least to most significant, allowing high leading zeroes. Construct the *reference* integer height h and carry c by h_0=c_0=0. On each digit let q=floor((x_i+c_i)/3), v=(x_i+c_i) mod 3 in {0,1,2}, using Euclidean division even if x_i+c_i=-1. Set:

    v=0: (h',c')=(h+1,q-1), charge 0
    v=1: (h',c')=(h-1,q),   charge 4
    v=2: (h',c')=(h-1,q+1), charge 2

Define the residue subset R_n by the finite, integer-only conditions

    h_i+c_i >= 0 for i=0,...,2n,
    h_(2n)=0 and c_(2n)=0.

Let Q(r) be the sum of the displayed charges along this reference path.

**Theorem.** Every r∈R_n, every a,d∈Nat, and every b≥1 satisfy the full, all-outcome **original B-drain equality**

    B(a,M*b+r,d)
      = B(a,b,d + 3*((M-1)*b+r) + Q(r)).

In particular, for every successful output the first counter is exactly unchanged by the prefix removal. Failure is unchanged as well. The residue set has exactly |R_n|=N_n elements. Its members are distinct integers, with no overlap within a fixed n.

## Proof of the full source identity

The one-level source reductions for positive b=3q+v are:

    v=0: B(a,3q,d)=B(a+1,q-1,d+6q+3)     (q>0)
    v=1: B(a,3q+1,d)=B(a-1,q,d+6q+7)   (a>0)
    v=1: B(0,3q+1,d)=none
    v=2: B(a,3q+2,d)=B(a-1,q+1,d+6q+5) (a>0)
    v=2: B(0,3q+2,d)=B(0,q,d+6q+7).

For b≥1 the first 2n source reductions all have positive block arguments, even with carry -1: before the final reduction the surviving high-place contribution is at least 3. Since -1≤c_i≤1, the remaining block is at least 2.

First take an initial first counter a≥1. From h+c≥0 and c≤1 we get h≥-1. If a+h=0 then necessarily a=1,h=-1,c=1. The only next reference move compatible with the nonnegative h+c condition is v=0, which succeeds at first counter zero. Hence every reference move is a legal original source move. At the end the first counter is a+h_(2n)=a and the residual block is b+c_(2n)=b.

For a=0, follow the same reference word while h≥0. The only possible discrepancy occurs when a reference v=2 reduction drops h from 0 to -1. It necessarily lands at c=1 and h+c=0. The real zero-first-counter rule instead leaves (first counter, carry)=(0,0). The following reference step must be v=0 to keep h+c nonnegative. It has next original input digit x=2, so the real zero-counter branch performs another v=2 reduction and returns to (0,0), exactly where the reference path returns. This **two-digit coupling** has identical total third-counter increment for both branches: writing the block before the pair as 9u+8, both routes add 24u+26 to d and reach block u. This is precisely the already original-source-proved ninefold residue-eight identity of [Agent 49](../agent49-parity623/ThirdNinefold.md). Repeating the coupling proves the statement for a=0.

In each ordinary reference reduction, the increment of d equals 3 times the decrease in the block count, plus the displayed charge 0, 4, or 2. The exceptional two-digit coupling has the same aggregate charge as its reference v=2,v=0 pair, namely 2. Summing all reductions gives the indicated shift 3*(M*b+r-b)+Q(r), independent of a. The argument applies equally when the remainder B(a,b,...) subsequently fails, establishing full Option equality. This completes the all-natural identity.

## Exact Catalan counting proof

Set k=h+c. Its transition depends only on k, carry c∈{-1,0,1}, and the next ternary digit. For each carry, the three digit choices yield (delta k, next carry):

    c=-1: (0,0), (+1,-1), (0,0)
    c= 0: (0,-1), (-1,0), (0,+1)
    c=+1: (-2,0), (-1,+1), (0,0).

Every length-L ternary word corresponds bijectively to one path of this transition system. R_n counts the length-2n paths from (k,c)=(0,0) to itself which never enter k<0.

Introduce formal power series A_k(t), B_k(t), C_k(t) counting all admissible continuations from height k with carries -1,0,+1 to final (0,0), one factor t per digit. First-step decomposition gives, with missing negative-index terms interpreted as zero,

    A_k = t*A_(k+1) + 2*t*B_k
    B_k = [k=0] + t*A_k + t*C_k + [k>=1]*t*B_(k-1)
    C_k = t*B_k + [k>=1]*t*C_(k-1) + [k>=2]*t*B_(k-2).

For A(x)=sum A_k*x^k and similarly B(x),C(x), write b_0=B_0. The boundary equations yield A_0=((1-t^2)*b_0-1)/t, and algebraic elimination of A(x),C(x) gives the **exact kernel equation**

    B(x) = (1-t*x)*(x-t*(1-t^2)*b_0)
           / ((1-t^2)*(x-t-2*t*x^2)).

The kernel has a unique formal root of positive t-valuation

    rho(t) = (1-sqrt(1-8*t^2))/(4*t)
           = t*Catalan(2*t^2).

Substitution is legitimate as a formal t-series: any path from level k to zero has at least ceil(k/2) digits, so each fixed t-degree has finite x-support. Its denominator must cancel at x=rho(t), forcing

    b_0 = rho(t)/(t*(1-t^2))
        = Catalan(2*t^2)/(1-t^2).

The coefficient of t^(2n) is sum_(j=0)^n 2^j Catalan(j). This proves the exact number of source-neutral residues **in R_n**, uniformly over n with no finite cutoff. Odd coefficients vanish. The square-root root is chosen by its zero constant term; no analytic convergence assumption is required.

## Reproducibility and remaining obligations

The [independent enumerator](catalan_neutral.py) verifies the coefficient formula through n=12 by a finite-state/height dynamic programme. It enumerates every member of R_n through n=4 and checks the full Option-valued transport identity against a separate exact one-level drain implementation for all initial first counters 0..2n+2 and positive suffixes b∈{1,2,5}. These bounded tests validate the implementation, while the universal statements follow from the displayed source identities and the proof above.

The earlier [Agent 49 communication](../../communications/agent8/20261109T063050Z_agent49-neutral-ternary-catalan.md) conjectured the *total* number of all-first-counter-neutral residues to equal these same N_n; that stronger exhaustiveness assertion requires an independent necessity argument for the k≥0 path condition. In particular, the theorem here supplies a **certified explicit subset of that cardinality**, not an unproved assertion that every other residue fails neutrality. The source's genuine blank-tape starting state D(0,7) is not shown to reach any prepared neutral block family; the original-root halting question remains open.
