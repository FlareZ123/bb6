# Obstruction to fixed congruence invariants for the canonical BMO5 graph

This is an all-band mathematical obstruction, not a claim about which genuine blank-root orbits halt. The canonical signed macro and its source closure are accepted in CI 45495152205. The core 3-adic lifting and density theorem below is also proved in Lean 4.36.0-rc2 (CapModLift.lean, CapModNoGo.lean, standard axioms). The arbitrary-mixed-modulus extension is a written proof using elementary finite cyclic group arguments; it is not yet a Lean declaration.

## The exact immediate terminal family is locally dense in unit residues

Put P(k)=5*2^k and F(k)=2P(k)+k. For any fixed r>=1, at sufficiently large k, if F(k)=3^r q and q is a 3-adic unit, then (k,q) is a canonical positive entry with positiveCount(k,q)=r-1 and positiveNext(k,q)=k+3. Indeed q has parity k, grows exponentially for fixed r, is at most 2P(k)-2, and 3^(r-1)q=F(k)/3<=2P(k)-2<3^r q. The negative weight is exactly 2k+3, hence it halts in band k.

For every s>=0, 2^(2*3^s)=1 (mod 3^(s+1)), by induction using the binomial cube. Consequently

    F(k+2*3^s*t) = F(k)+2*3^s*t (mod 3^(s+1)).

At each new digit precision the three choices t=0,1,2 give all three lifts. Thus for either parity there is a root residue of F modulo 3^h for any h. If F(k0)=0 (mod 3^h), h>=1, and u is any unit modulo 3^h, fix r=h+1 and lift to F(k)=3^r*u (mod 3^(r+h)) while keeping k=k0 (mod 2*3^h). Arbitrarily large k can be chosen by adding multiples of 2*3^(r+h). Then q=F(k)/3^r is a unit with q=u (mod 3^h), and is an actual immediate terminal entry by the previous paragraph.

This is the Lean theorem terminal_residue_dense: every such pair of band/coordinate residue classes has arbitrarily large genuine canonical terminal states. The theorem no_periodic_barrier excludes a predicate periodic in k modulo 2*3^h and q modulo 3^h, covering a unit residue in every sufficiently high band and excluding all canonical halts. These are universal quantifiers, not a finite search.

## Arbitrary fixed mixed moduli: no inductive safety invariant

**Theorem (written proof).** Let I(k,q) be a predicate whose truth for all sufficiently large band indices depends only on k modulo a fixed positive integer L and q modulo a fixed positive integer M. Assume:
1. I contains a valid canonical positive entry in at least one sufficiently high band (equivalently, in arbitrarily high bands by periodicity).
2. For every valid canonical positive entry (k,q) with I(k,q), its signed event is nonterminal and its positive return (j,v) satisfies I(j,v).

Then no such I exists. In particular a fixed congruence-only inductive invariant cannot prove nonhalting of any of the three canonical anchors. Finite exceptions in the initial bands do not help, since a nonhalting signed orbit has strictly growing band indices.

**Proof.** Refine the coordinate modulus without weakening periodicity so that M=3^h*m with h>=1, m even and coprime to 3. Refine L to an even multiple at least 4 of its old value and 2*3^h, also a period of 2^k modulo M for sufficiently large k (the 2-primary part vanishes, and the odd part is a finite unit group). Write c_k=3-10*2^k as an integer. All residue calculations below take place above the finite periodicity and realization thresholds.

First produce a unit-coordinate class in I. If its supplied canonical state is a unit, done. Otherwise shift its band arbitrarily high within its period, and choose two consecutive representatives of its coordinate residue in [k+6,k+6+2M), both divisible by three and of parity k. For large k these are canonical, as their values are below 3(k+6) and 2P(k)-2. At most one can have an exceptional relaxed exit. Indeed the exceptional condition for exponent a=positiveCount+1 is

    2P(k)-1 <= 3^a q <= 2P(k)+k+3.

The ratio of the two q values is <2, while the ratio of the interval endpoints is <3/2. Therefore if both are exceptional their exponents must agree (otherwise their powers of three would have ratio at least 3). At fixed exponent the interval has width k+4, but 3^a >= (2P(k)-1)/(k+6+2M) > k+4 for all sufficiently high k. The two distinct integers q cannot both fit. The ordinary positive return has coordinate p=3^a q+c_k, a unit modulo 3. Closure gives a unit class in I.

For any unit coordinate class at any band phase, every fixed exponent a>=1 can be realized as an ordinary return from a sufficiently large actual canonical state in that same class: choose q of the required residue in

    (2P(k)+k+4)/3^a <= q <= (6P(k)-6)/3^a.

The interval length grows exponentially in k, as does its lower endpoint; it eventually contains a representative of every allowed unit residue and has q>=k+6. Its upper bound gives 3^(a-1)q<=2P(k)-2 and its lower bound gives 3^a q>2P(k)-2 and p>=k+7. This proves exact realization and closure, not an abstract overapproximation assumption.

Choose a>=h with 3^a=1 (mod m), possible since 3 is a unit in the finite group modulo m. The exponent a+1 gives multiplier 3 (mod m). Both exponents erase the coordinate modulo 3^h and set the next coordinate to c_k modulo 3^h. Hence after one such step the invariant has a nonempty forced 3-adic class. At each later band phase it is closed under the two modular edges on the m-coordinate

    x -> x+c_k,       x -> 3x+c_k,

with the 3^h-coordinate fixed to c_k at the next band. Both edges are genuine regular transitions on representatives as proved above. Since L is even, complete periods preserve parity.

At a fixed band phase, let S be the nonempty set of m-residues in I whose 3^h-residue is the forced one c_(k-1). Every full L-step sequence of these edges is a permutation of the m-residues of the correct parity; its image of the finite set S is contained in S, hence equals S, and the inverse also preserves S. Put C=sum_{t=0}^{L-1} c_(k+t) and A_t=sum_{i=0}^{t-1} c_(k+i). The all-additive word gives T(x)=x+C. A word using the multiplier 3 only at position t gives T_t(x)=3x+C+2A_t. Therefore T^(-1)T_t(x)=3x+2A_t preserves S in both directions. Composing the t+1 version with the inverse of the t version shows that translation by 2c_(k+t) preserves S. We have t=0,1 available because L>=4. The identity c_(k+1)=2c_k-3 and gcd(m,3)=1 give gcd(c_k,c_(k+1),m)=1. Thus the two translations generate the complete even subgroup modulo m (Bezout). Since S is nonempty, it is the entire parity class. All other band phases inherit this property by the all-additive edges, which bijectively transport their parity classes and force the next 3-adic residue.

Finally take a root residue k0 of F modulo 3^h, with k0>=1, and choose u=c_(k0-1) modulo 3^h. It is a unit. The preceding lifting theorem gives arbitrarily large canonical immediate terminal entries (k,q) with k=k0 (mod 2*3^h) and q=u (mod 3^h). The forced residue c_(k-1) equals u since 2*3^h is a period modulo 3^h. At the actual phase k modulo the refined L, every m-residue of parity k is in S, so the residue of q is included. By CRT and periodicity, I(k,q) holds. But this event is terminal, contradicting condition 2. QED.

## Scope

The theorem excludes a fixed finite residue-state invariant even when it handles safe negative excursions, and even when it permits arbitrary finite initial exceptions. It does not exclude automata on the complete digit strings, nonperiodic or growing-modulus invariants, history-dependent certificates, or analytic estimates. It does not imply that any actual blank-root trajectory ever reaches a terminal state.

The proof depends on exact realization of both chosen exponent branches; it does not treat the full-branch real limit as the actual integer dynamics. The modular group argument is elementary and uses only finite permutations, not an equidistribution assumption about the authentic orbits. This is an intermediate mathematical result with independent novelty review pending.
