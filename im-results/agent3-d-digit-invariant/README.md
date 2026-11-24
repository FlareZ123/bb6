# D: deterministic Benford law and positional automatic invariant obstruction

2026-11-24, Agent 3. A mathematical consequence of the global affine source reduction and the existing density-one/phase certificates. The generic finite-state and density arithmetic core is kernel-checked; the real-variable asymptotic argument and source composition are supplied below as paper proofs. No genuine root decision or BB(6) numerical bound.

## 1. Exact asymptotic phase and all-base leading digits

Put a=8/3. For any infinite selected return path from n_0>=5, use the phase inequalities in [phase separation](../../results/2026-11-24-d-four-root-phase-separation-agent3.md). The normalized lower endpoints l_t=(5n_t-23)/a^t are nondecreasing, and u_t=(5(n_t+R_t)+27)/a^t are nonincreasing. Their gap (5R_t+50)/a^t tends to zero because R_t<=R_0+11t. The nested intervals converge to a common 5lambda>0. In particular

    lambda*a^t - R_t - 27/5 <= n_t <= lambda*a^t + 23/5.

This proves n_t=lambda*a^t+O(t) for each individual infinite path, without any distributional assumptions about the residue itinerary. For any integer base b>=2, log_b(a) is irrational: a rational value p/q>0 would imply b^p*3^q=8^q. Therefore

    log_b(n_t) = t*log_b(a)+log_b(lambda)+o(1).

The fractional parts are uniformly distributed modulo one by the elementary irrational-rotation theorem. For completeness, every nonconstant integer Fourier mode of the unperturbed sequence has vanishing mean by the geometric-series formula; the o(1) perturbation does not change these means. The Weyl criterion (or trigonometric approximation of interval indicators) gives uniform distribution. Consequently for every canonical base-b leading block whose integer value is p>=1, the frequency of that block is exactly log_b((p+1)/p). Every block occurs infinitely often. This statement is conditional on an infinite path, not a prediction of the time to halt.

## 2. Generic regular-language obstruction

A zero-natural-density set of integers recognized by a finite positional DFA excludes a complete leading-prefix cylinder. In fact, for an N-state MSD-first DFA, **every** canonical prefix has an extension of fewer than N digits to a dead state (one from which no accepting continuation exists).

Proof: suppose a prefix reaches a state from which no dead state is reachable. Each extension of that prefix by k arbitrary digits can be completed to acceptance with fewer than N further digits: choose a shortest accepting path, which has no repeated state. The b^k extensions yield distinct accepted canonical integers, because they all have the same initial length and distinct prefixes, even if completion lengths differ. All these integers are below b^(length(prefix)+k+N). This contradicts zero density as k tends to infinity. A shortest path to a dead state then also has fewer than N digits. The accompanying Lean proof uses an equivalent finite-affine-preimage density argument and verifies the short-dead-extension statement directly.

A stronger time-frequency consequence follows. Among canonical prefixes of length 1+jN which can extend to acceptance, there are at most (b-1)*(b^N-1)^j, since at least one N-digit extension from every coaccessible reachable state leads to a dead state. The Benford measure of each such prefix cylinder is at most b^(-jN)/ln(b). Thus their total measure tends to zero. By the leading-digit theorem, on every infinite D return path the frequency of n_t belonging to any zero-density base-b automatic set is zero. This remains true for a finite union of such sets using different integer bases.

## 3. Application to safe finite-state invariants

By [density-one halting](../../results/2026-11-24-d-density-one-agent3.md), every fixed suffix's nonhalting counter set has natural density zero. A sound invariant must have every counter fiber contained in this set (the finitely many n<2 are irrelevant).

For any DFA over a separately encoded positional counter and suffix, with either field first, there are only finitely many possible counter fibers: the first suffix field can determine only the starting state, or the last suffix field only the accepting subset of states. The same argument applies if the representation is LSD-first, by regular-language reversal. Each realized fiber has zero density by safety, hence their finite union is regular and zero density. An infinite trajectory accepted by such a DFA would stay within that union, contrary to Sections 1–2. This rules out all sound inductive invariants of this kind through any of the four genuine roots, without a bound on state count. More generally, a finite collection of fixed-base regular languages for each suffix (even a finite set of bases) cannot cover an infinite trajectory soundly. The finite union argument applies to finitely many distinct languages overall, not to an unbounded number of automata indexed by arbitrary suffixes.

## 4. Joint synchronous automata

For a DFA reading paired counter digits (LSD first in base b) and suffix symbols with padding once either field ends, let ell(s) be the number of suffix symbols including any end marker. For every state q realized after the suffix is exhausted and exactly ell(s) low digits of some counter have been read, fix one such concrete (s,low) context. The regular language of canonical nonempty high-part counter words accepted from q with padded suffix symbols corresponds to integers h for which n=b^ell(s)*h+low is accepted with that fixed s. Soundness and the finite-affine-pullback lemma imply this high-part language has zero density. There are finitely many such q. Their union is regular (reverse to MSD order) and zero density.

If the unprocessed high digit length digits_b(n_t)-ell(s_t) tends to infinity, every sufficiently late occurrence of the union's forbidden leading prefix contradicts acceptance. In fact, the prefix-entropy bound in Section 2 shows that for a fully accepted infinite path, the upper time density of times with unprocessed high length >=L tends to zero as L tends to infinity. For fixed L, such times have their leading L digits in the extendable-prefix set of the zero-density high language; apply the exact Benford distribution and let L grow.

In particular, encode the suffix in fixed blocks of eight bits (with constant end-marker overhead) while reading the counter in binary. Since ell(s_t)<=1+R_t/8+O(1) and R_t<=R_0+11t, while digits_2(n_t)=t*log_2(8/3)+O(1), the high length tends to infinity: 11/8<log_2(8/3) follows from 2^11*3^8<8^8. Thus this entire synchronous packed class is excluded as well. A one-bit-per-digit synchronous encoding is not excluded by this unconditional width bound. Such a candidate would require the suffix to be nearly as long as the binary counter at almost all times, in the time-density sense just proved. A future tighter deterministic width bound or a positive-density short-suffix theorem would eliminate it too.

## 5. Kernel-checked discrete core and reproduction

Run `bash reproduce.sh` with Lean 4.36.0-rc2. The exact compressed source decodes to SHA256 964293fdaa19b2e5ce26556c3870d8c52d9a7703bcea9e6beeea0aa10cd9920f. Namespace BB6.Agent3.DigitInvariant contains:

- Sparse: zero density via all bounded finite nodup witness lists; sparse_subset, sparse_union, sparse_affine and sparse_fin_union.
- finite_affine_holes and sparse_interval_hole, with no probabilistic assumptions.
- short_accept: shortest accepted continuation has length < N, by nodup state trace and finite cardinality.
- exists_digits, fixed_digits, value_append, value_bound: positional integer representation and affine concatenation.
- sparse_regular_missing_prefix, sparse_regular_short_dead_extension, sparse_regular_short_missing_prefix, no_sparse_digit_invariant.

All eleven exported axiom audits gave only standard propext, Classical.choice, Quot.sound (some omit choice); no sorryAx. The Lean theorem no_sparse_digit_invariant takes dense leading-prefix occurrence and numerical sparsity as explicit premises. The source-specific phase and density instantiation, Benford frequency argument, finite fiber reasoning and packed synchronous extension above are rigorous paper compositions rather than a new end-to-end original-source Lean import.

## Unresolved

None of these implications gives an authentic terminal or nonhalting witness. A sound invariant with unbounded fiber-state complexity, nonregular arithmetic relations between n and s, or a sufficiently long synchronous suffix field may still be possible. Exploratory 9/12-bit weighted-width abstract graphs admitted spurious high-gain E cycles because the exit abstraction forgets correlations beyond the prefix. No deterministic width slope below log_2(8/3) is claimed for raw one-bit synchronous fields. The focus should shift to a genuinely nonregular arithmetic/root mechanism rather than attempting increasingly expressive *finite-state* variants already ruled out by this theorem.
