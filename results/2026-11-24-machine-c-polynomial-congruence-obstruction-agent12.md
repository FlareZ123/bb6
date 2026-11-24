# Machine C: polynomial concentration and polynomial-congruence safety obstruction

**Agent 12, 24 November 2026.** This strengthens the [semilinear obstruction](2026-11-24-machine-c-semilinear-obstruction-agent12.md) to a larger class of counter invariants. The exact modular uniqueness lemma used in the counting argument is kernel-checked in [Concentration.lean](../im-results/agent12-c-high-shadow/Concentration.lean) (Lean 4.36.0-rc2, standard axioms only). The asymptotic counting and polynomial sign arguments are written mathematics, not an end-to-end Lean theorem.

## Theorems

**Polynomial concentration.** Let (a_i,k_i) be any infinite successful orbit of the original Machine C section map and M_i=a_i+2k_i. For any finite set S of real ratios in [0,1], any constants C>0 and epsilon>0, it is impossible that

    min_{s in S} |a_i/M_i-s| <= C M_i^(-epsilon)

for all sufficiently large i.

**Polynomial-congruence obstruction.** No nonempty terminal-free forward-closed subset of the two section counters is definable by a finite Boolean combination of polynomial sign/equality predicates and polynomial congruences modulo fixed positive integers.

The theorem is conditional on infinite orbits where relevant; it does not show the blank orbit is infinite or finite. In particular polynomial-congruence safety invariants are strictly more general than linear inequalities plus fixed congruences, but still do not encompass arbitrary computable invariants or richer configuration representations.

## 1. Uniform shift and mass estimates

Use A=a,M=a+2k. Strict mass growth by at least two is [source-verified](../im-results/agent3-c-bounce-inverse/SectionMassStrict.lean). After finitely many steps k>=1 and bounded special cases disappear. On ordinary regular-input shifts r>=1, the equations are

    A'=2^r A-M+b, M'=M+3r+1,

where b depends only on r and parity. At bounce depth n, r=n+2. Exceptional c=4 even exits have the same affine form with mass increment 3r-1 and output A'=M'-6. On the special a=0 or 1 bounces at large M, the ordinary mass increments are respectively 3r+3 and 3r+4 and the output has the same affine form A'=2^r A-M+b (the input A is fixed by the label). All these formulas follow from the exact [bounce recurrence](../im-results/agent46-c-jump/BounceCalc.lean) as in the earlier proofs.

Uniformly on all sufficiently late successful edges, r=O(log M): the initial middle K>=1, height c<=M+3, each recursive call decreases c by at least 2K and doubles K or more, so after n calls at least 2(2^n-1) height has been consumed. Thus mass increases by at most O(log M) per edge.

When A<=C M^(1-epsilon), with 0<epsilon<=1 (reduce larger epsilon to 1), an ordinary bounce at large M must have

    r >= epsilon log_2 M-O(1).

Indeed the exit bound has 2^r B>=M+3r+constant, where B=A+2+o (regular, o=A mod 2), or B=4,8 for a=0,1. Since B=O(M^(1-epsilon)), the inequality follows. Direct is impossible in this near-zero region for sufficiently large M.

## 2. Finite limiting directions force frequent near-zero visits

Assume the claimed polynomial concentration for an infinite orbit. Its actual accumulation set of ratios is a nonempty finite subset of S; discard other members, which are avoided eventually. Call the remaining set S again. Each late ratio is assigned to its unique closest member of S, with error at most C M^(-epsilon).

First 1 cannot be an accumulation ratio. If a sequence of states has A/M tending to 1, then k/M tends to 0. From such a state the direct guard holds for arbitrarily many consecutive edges as M grows, because on j direct edges k_j=2^j(k+2)-2, M_j=M+4j. The maximal direct run is always finite (a decreases by at least two per edge), and at the first non-direct state its gap 1-A/M=2k/M lies in (1/2,1]. Extract a subsequence whose final gap converges to g in [1/2,1]. For every fixed j, the state j direct edges earlier exists along that subsequence for sufficiently long runs, and its gap tends to g/2^j by the exact direct equations. This yields infinitely many distinct accumulation ratios 1-g/2^j, contradiction.

Thus exceptional c=4 exits occur only finitely often, since they give A'/M'=1-6/M'. For each positive s in S, r is uniformly bounded when A/M approaches s: either direct or K grows linearly with M and each recursion consumes at least 2K. Along any subsequence assigned to s with fixed r, the exact affine formulas give output limiting slope 2^r s-1. Since it must lie in [0,1) (1 is excluded), exactly one r>=1 is possible, namely the unique r with 2^-r<=s<2^(1-r). Therefore on the tail the assigned positive s determines the shift r, and the next assigned member is

    f(s)=2^r s-1 in S.

This argument includes dyadic boundaries: the other neighboring branch would yield limiting slope 1, already excluded. Uniformity follows by finiteness of S and the bounded set of shifts for its positive members.

If the directed graph s->f(s) on positive members has a cycle, any sufficiently late occurrence of that cycle must follow it forever. A full shift word then repeats, with parity repeating after one or two traversals since ordinary mass increments are fixed by shifts. The complete branch itinerary would be eventually periodic, contrary to [the aperiodicity theorem](2026-11-24-machine-c-aperiodic-section-itinerary-agent12.md). Every member of S is an actual accumulation ratio, so no positive cycle exists. Hence 0 belongs to S, and between consecutive visits assigned to 0 there are at most |S| positive-member edges. Near-zero visits occur with bounded gaps in section index.

## 3. Modular uniqueness bounds the number of near-zero visits

Fix a large real X, and consider all near-zero visits with starting mass in [X,2X]. There are at least c X/log X such visits, for some c>0 and all sufficiently large X: the orbit crosses the band with individual mass increments O(log X), and near-zero visits have bounded gaps in index. More formally the first mass at or above X is at most X+O(log X), and the last mass before exceeding 2X is at least 2X-O(log X). Partition this segment into bounded-index gaps to obtain the lower bound.

Choose a fixed positive integer H with H epsilon>2. From each such near-zero visit, look forward to the H-th subsequent near-zero visit. There are at most J=H(|S|+1) edges in the resulting block. For X large its final mass is at most 3X: a fixed number of edges, each with O(log M) mass increment, cannot increase mass from 2X to 3X. The H outgoing near-zero edges each have shift at least epsilon log_2 X-O(1). The total shift R therefore satisfies 2^R>X. All shifts in the block are O(log X), and all non-shift label components have finitely many possibilities. Hence the number of complete label words of length at most J is O((log X)^J).

For any fixed such word, compose its exact affine equations:

    A'=P A-Q M+C_0, P=2^R, Q odd.

The oddness of Q follows from Q_new=2^r Q_old+1. This is valid also for the special a=0,1 labels, since their exact affine extension has the same -M coefficient. For a given endpoint value A', the congruence

    Q M = C_0-A' mod P

has a unique mass residue, since Q is odd. The interval [X,2X] has length X<P, so there is at most one possible starting M in that interval for each endpoint A'. The Lean theorem endpoint_determines_mass proves exactly this uniqueness from two affine endpoint equalities and mass difference less than 2^R.

The block endpoint is a near-zero visit, and its mass is at most 3X, so 0<=A'<=C(3X)^(1-epsilon). Thus for each fixed word there are at most O(X^(1-epsilon)) possible starting masses. Taking the union over words gives at most

    O(X^(1-epsilon) (log X)^J)

near-zero starting masses in [X,2X]. Strict mass growth makes all actual visit masses distinct. Comparing to the lower bound cX/log X gives a contradiction because X^epsilon/(log X)^(J+1) tends to infinity. This proves the concentration theorem.

Notice the essential feature: a bounded number of near-zero excursions supplies enough total binary shift to separate every possible mass in the band, while only polynomially many endpoint values and polylogarithmically many words are allowed. No finite simulation or statistical orbit hypothesis is used.

## 4. Polynomial-congruence sets avoiding prepared halts must be polynomially narrow

Suppose a terminal-free forward-closed set U is given by a finite Boolean formula of polynomial signs/equalities and polynomial congruences modulo fixed positive integers. Work in (A,M) for sign predicates by substitution k=(M-A)/2; rational coefficient denominators can be cleared by positive constants. Let N be a common multiple of all moduli. Every congruence truth value is fixed on each original counter residue class modulo N.

For each nonzero nonconstant sign polynomial P of total degree d, write p(s) for its leading homogeneous part evaluated at (s,1), a nonzero univariate polynomial. Uniformly for 0<=s=A/M<=1,

    P(A,M)/M^d = p(s)+O(1/M).

Let Z be the union of 0,1 and all real roots of these finitely many p in [0,1]. It is finite. Set D=max(1,maximum total degree). By polynomial factorization and compactness there is c>0 with |p(s)|>=c dist(s,Z)^D for every p and s in [0,1]: the multiplicity at each root is at most D, and away from the roots the minimum is positive. Thus outside strips dist(s,Z)<=C M^(-1/D) for a sufficiently large common C, every polynomial sign is determined by the leading sign on the component of [0,1]\Z containing s (nonzero equalities are false there). Constant or identically zero polynomials have fixed truth values.

Fix a residue class and an interior component of [0,1]\Z. If its leading-sign/residue truth pattern were accepted by the formula, then all sufficiently large points of that class in any smaller open interval inside the component would belong to U. But [the prepared halting-ray theorem](2026-11-24-machine-c-semilinear-obstruction-agent12.md) constructs an infinite ray of actual prepared halting states in every such class and interval. A terminal-free forward-closed U cannot contain any of them, since their finite trajectories reach terminal states. Therefore no such truth pattern is accepted.

It follows that every sufficiently large point of U lies in the shrinking strips around Z with exponent 1/D. If U is nonempty, forward closure and absence of terminals generate an infinite successful orbit in U, contradicting the concentration theorem. QED.

## Scope

This excludes a finite polynomial-sign/fixed-congruence Boolean language for global safety invariants in the section counter plane, including finite affine-line and semilinear invariants as special cases (the semilinear obstruction also has its independent direct proof). It does not prohibit arbitrary nonpolynomial functions, infinitely many congruences, more general logical quantifiers, or a root-specific halting/nonhalting certificate. The authentic blank stopping-parameter existential remains open.
