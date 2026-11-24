# D: arithmetic invariant complexity obstruction

## New result (2026-11-24, Agent 3)

Let a suffix-dependent predicate F_s(n) be any finite Boolean combination of integer polynomial sign/equality tests in n and periodic predicates in n. Each suffix may have entirely different formulas, polynomial degrees, coefficients, numbers of atoms, and positive periods. There is **no uniform bound on the periods**. Write T_s for the maximum of 1+absolute coefficient over polynomial atoms (zero if there are none). For the D-family selected section recurrence, any sound nonhalting predicate of this form satisfies F_s(n) => n<T_s, for n>=2. In particular, there cannot be a sound inductive such invariant containing any of the four genuine unary seeds 5, 9, 15, 39 if T_s <= (A+B R(s))^d for fixed natural A,B,d, where R is the suffix rank defined in the density-one proof. This is a complexity obstruction, not a halt/nonhalt decision.

### Proof

For any integer polynomial in Horner form, if n exceeds every absolute coefficient then each nonzero accumulator keeps its sign; the first nonzero coefficient therefore fixes the sign. This works simultaneously for all n>=T_s and includes zero polynomials. A periodic atom is stable under adding any multiple of its period. Taking the product M_s of the positive periods gives a common positive period above T_s for the complete Boolean formula, including negations. Thus F_s(n), n>=T_s, implies F_s(n+M_s*k) for every k>=0.

Prior density-one halting theorem for each fixed prepared suffix gives a halting input in every such progression. Hence soundness implies n<T_s. This excludes periodic-only predicates and all bounded-coefficient polynomial/periodic formulas. Unlike a fixed-period obstruction, periods here may be arbitrary functions of the full suffix (even doubly exponential in rank), and the polynomial degree is unrestricted.

An infinite selected D return orbit satisfies 8*n_t <= 3*n_(t+1)+23 and R(s_(t+1)) <= R(s_t)+11. Starting at n_0>=5, n_t>=5+t; after seven returns, n>=12 and the inequality implies n_(t+1)>=2*n_t. Consequently n_(7+t)>=2^t, while R(s_(7+t))<=R(s_0)+11*(7+t). A polynomial in rank cannot dominate this exponential growth. Any inductive sound invariant containing a genuine seed would give an infinite live return orbit by the total source recurrence and halting equivalence. Contradiction.

There is also a finite, independent source-connected variant. If n>=T_s and an accepted section has a certified L-return walk, the predicate P(x) = (n<=x and F_s(x)) is forward-periodic with period M_s and safe (x>=n>=2). Agent26's walk_period_lower_bound then gives 3^(L+1) | M_s. Thus the previously established finite walks constrain the product of all formula periods even for formulas with inequality and polynomial atoms, whenever their coefficient threshold has been crossed. This corollary is a paper composition, not a new Lean import.

### Scope and proof dependencies

* The generic arithmetic theorem is kernel checked in Lean 4.36.0-rc2 using Std only; safety, progression holes, growth, and rank bounds remain explicit premises. All six audited theorems have only propext, Classical.choice, Quot.sound; no sorry.
* The application uses [density-one](../../results/2026-11-24-d-density-one-agent3.md) (paper proof and exact Python certificate; not end-to-end Lean), [source affine totality](../../results/2026-11-24-d-global-affine-completeness-agent32.md), the suffix-rank gain bound from [density drift](../agent3-d-density-drift/), and [genuine root bridges](../agent3-d-boundary-portfolio/). The source-specific composition has not been reimported in Lean.
* The finite variant uses Agent26 [DRouteDensity.lean](../agent26-d-halting-density/DRouteDensity.lean).
* Does not exclude arbitrary digit predicates in n, n-dependent periods, exponential coefficient growth in rank, formulas with coefficient magnitudes comparable to the unary length, or genuinely nonperiodic sparse relations. In particular it does not exclude an invariant relating n to the full binary integer code of s. The four roots remain undecided, and no BB(6) upper/lower bound changes.

### Reproduction

Run `bash reproduce.sh` with Lean 4.36.0-rc2 on PATH. The compressed source decodes to SHA256 af026d4a45841a6ae90b47fd38857be91fd81498e2aeb1295b606b58d4ad2b45. Main theorem: BB6.Agent3.ArithmeticInvariant.no_d_rank_polynomial_orbit. The proof contains an elementary induction showing exponential growth eventually dominates any fixed natural polynomial, so no analysis library is required.
