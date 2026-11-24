# Fatal-reaching heights are dense in every fixed modular/interval cylinder

**Status, 2026-11-24 — paper theorem over the complete source-accepted ResetParent grammar.** This is an obstruction to an entire class of prospective #746 nonhalting proofs. It is not a blank-root decision, a proof of BB(6), or a new Lean-kernel acceptance. The source equations are those of [FirstInverseComplete.lean](FirstInverseComplete.lean), [ResetChain.lean](ResetChain.lean), and the equivalent unified arithmetic in [PeriodicReset.lean](PeriodicReset.lean). Exact finite examples and the composite-modulus selector are reproduced by [modular_cylinder_witness.py](modular_cylinder_witness.py).

## 1. Statement

Write F_n = 4*2^n - n - 4 and G(n) = 2 F_n + 5 = 8*2^n - 2*n - 3. At a nonfatal reset height h, let k be the sweep level and x = (h+k+4)/2^k. The exact source band is

    4*2^k < h+k+4,   h+k+5 < 8*2^k.

For natural h,u,k,a, a genuine first reset h -> u is characterized by this band and

    2^(a+1)*(2*u+5) = 3^a*(2*h+5+16*2^k+2*k+5).            (1)

Equivalently,

    h = 2^a*(2*u+5)/3^a - 8*2^k - k - 5.                 (2)

This is the entire grammar: a=0 is the even arm, a=t+1>0 is the odd arm. The ratio on the right of (2) is integral for every such edge.

**Theorem (arbitrary modular-cylinder fatal reachability).** Fix any positive moduli M,m, residues kappa,r, any nonempty real open interval I contained in (4,8), and any lower bound K. There exist natural h,k with k>=K, satisfying the strict source band, such that

    k = kappa (mod M),   h = r (mod m),   (h+k+4)/2^k in I,

and a genuine ResetParent chain from h to F_n for some n>=50001 with n=4 (mod 6). In fact the chain has at most v2(m)+1 reset edges, and k can be made arbitrarily large. No claim is made that the constructed h is reachable from 2.

Consequently a nonhalting invariant for the reset dynamics cannot be expressed by any finite Boolean combination of fixed congruences on h and k, comparisons of x with finitely many real constants, and bounded-level exceptions. This rules out a fixed finite modular/high-interval abstract domain, even with arbitrary composite moduli. It does not rule out relational invariants whose precision grows with k, nonlocal histories, or general automata on the physical tape.

## 2. Two modular facts

### 2.1 Unique gate root in each parity and freely tunable quotient

This section is independently kernel checked in [ModularCylinderHensel.lean](ModularCylinderHensel.lean), Lean 4.36.0-rc2, with standard axioms only. The remainder of the cylinder theorem is a paper proof.

For s>=0 and nonnegative integer t, binomial induction gives 4^(3^s t)=1 (mod 3^(s+1)). Therefore

    G(n+2*3^s*t) - G(n) = -4*3^s*t (mod 3^(s+1)).         (3)

For fixed parity, start with the unique class modulo 2. Equation (3) gives exactly one lift among the three possible digits at every next ternary precision. Hence G(n)=0 (mod 3^a) has exactly one class modulo 2*3^a in each parity. Denote the even one by N_a. For a>=1, N_a=4 (mod 6), since G(n)=2-2n (mod 3) for even n.

Moreover, along an arithmetic progression n=n0+2*3^a*c*t with 3 not dividing c and G(n0)=0 (mod 3^a), the quotient G(n)/3^a assumes every residue modulo 3^e, for any finite e. At lifting stage j, shift n by 2*3^(a+j)*c*t; equation (3) shifts the quotient by -4*3^j*c*t modulo 3^(j+1). The three choices t=0,1,2 give all next digits. Each selected quotient residue therefore holds on a further infinite progression.

### 2.2 Surjective exponential-linear congruence with arbitrary composite modulus

Let q be positive and coprime to 6. For arbitrary integers A,B and a prescribed delta modulo a 2,3-smooth modulus L0, there exists a residue class of delta modulo

    L = lcm(L0,q,phi(q))

such that

    A*2^delta - 2*delta = B (mod q).                      (4)

Here phi(1)=1. Proof: assign all prime-power coordinates of L in ascending prime order, retaining the prescribed 2- and 3-adic digits. For a prime p dividing q, p>=5. The already assigned smaller-prime coordinates determine delta modulo p-1. To solve modulo p^j, the exponential 2^delta modulo p^j depends only on delta modulo (p-1)*p^(j-1), which has already been fixed by the preceding digits. The new p-adic digit of delta enters -2*delta bijectively. Thus there is a unique next digit making (4) hold modulo p^j. Induct through v_p(q), then assign any extra digits required by L. Primes not dividing q impose no additional equation. The Chinese remainder theorem assembles the coordinates. This works even when one prime factor of q divides another's multiplicative-order modulus; treating the prime factors as independent without assigning smaller primes first would not suffice.

## 3. One-edge fatal predecessors with arbitrary odd congruence

We first prove the theorem with an arbitrary odd height modulus Q, and strengthen it to allow arbitrarily large valuation a. Write Q=3^e*q, gcd(q,6)=1. Refine the sweep-level class to k=kappa0 (mod M0), where M0 is a multiple of M,2,Q,phi(Q),q,phi(q). Any representative extending the desired original class is permitted. Let s=v3(M0), L0=gcd(M0,2*3^a)=2*3^s for a>=s. Choose even gate roots N_a throughout.

We want n=k+delta and G(n) divisible by 3^a. Compatibility of the two progressions n=N_a (mod 2*3^a) and n=kappa0+delta (mod M0) requires exactly

    delta = N_s-kappa0 (mod L0).                          (5)

Restrict a to positive multiples of phi(q); then (2/3)^a=1 (mod q). The desired source residue h=r (mod q) for the direct predecessor (2), with u=F_n, is equivalent to

    8*2^kappa0 * 2^delta - 2*delta
          = r + 8*2^kappa0 + 3*kappa0 + 8 (mod q).         (6)

All reductions of 2^k and k modulo q are fixed by M0. By Section 2.2 choose one class delta=d0 (mod L) satisfying (5) and (6). Neither L nor d0 depends on a once a>=s and a is a multiple of phi(q).

Let lambda=log2(3/2), which is irrational: a positive rational equality lambda=v/w would imply 3^w=2^(v+w). For n=k+delta and fixed a,delta, the normalized predecessor from (2) satisfies

    (h+k+4)/2^k
      = 8*2^(delta-a*lambda) - 8
        - ((2/3)^a*(2*n+3)+1)/2^k.                       (7)

The limiting value lies in any given open I contained in (4,8) exactly when delta-a*lambda lies in a corresponding nonempty open interval J contained in (log2(3/2),1).

Multiples of an irrational number are dense modulo every positive integer, including along any fixed arithmetic progression of the multiplier. For completeness: by pigeonhole, arbitrarily long finite lists of fractional parts contain two within any epsilon, producing a nonzero group element of size <epsilon modulo the period; successive multiples of that element form an epsilon-net. The closure of nonnegative multiples is the same as that of integer multiples, since arbitrarily large positive multiples approach zero. Translation and deletion of finitely many terms preserve density. Apply this to a restricted to multiples of phi(q), modulo L. There are arbitrarily large a and positive delta=d0 (mod L) with delta-a*lambda in J. Fix one such pair, taking a>=s and as large as any prescribed threshold.

By CRT, (5) gives an infinite progression of n with n=N_a (mod 2*3^a) and n=kappa0+delta (mod M0). Its step is 2*3^a*c with 3 not dividing c. In particular n=4 (mod 6). The values of k=n-delta and 2^k modulo 3^e are fixed on this progression. Section 2.1 now permits an additional progression on which

    G(n)/3^a = 2^(-a)*(r+8*2^k+k+5) (mod 3^e).

This gives the required h residue modulo 3^e; (6) gives the residue modulo q, hence modulo Q. Define h exactly by (2). For arbitrarily large n on the final progression, k>=K, h>=0, and (7) lies strictly inside I, with enough margin for h+k+5<8*2^k. Equation (1) holds identically, proving an actual ResetParent h F_n. The quotient G(n)/3^a is odd, so for k>=a the exact valuation v2(h+k+5)=a. This also establishes arbitrary-high-valuation density in the zero-low-bit class, with any odd residue.

## 4. Recovering every low-bit cylinder in at most v2(m) prefix edges

Write m=2^b*Q, Q odd. If b=0, Section 3 already proves the theorem. Otherwise refine the initial level class to fix k0 modulo lcm(M,2^b); throughout the construction k0 can tend to infinity in this class. Set l_0=b and r_0=r modulo 2^b. Choose an irrational x0 in I.

We construct a finite *limiting* prefix of tokens (a_i,delta_i), where delta_i=k_(i+1)-k_i and k_i=k0+D_i, D_i=sum of earlier deltas. At each step l_i is the remaining initial binary precision and h_i=r_i (mod 2^l_i) is required. While l_i>0:

* If r_i+k_i+5=0 (mod 2^l_i), choose a_i=l_i and l_(i+1)=0.
* Otherwise choose the unique a_i<l_i determined by the valuation of r_i+k_i+5 modulo 2^l_i. Let l_(i+1)=l_i-a_i-1. If positive, define the next required residue by

      r_(i+1) = (3^a_i*((r_i+k_i+5)/2^a_i)-5)/2
                    (mod 2^l_(i+1)).

  In this formula use a fixed nonnegative representative of k_i modulo 2^b; the quotient is odd before subtracting 5 and the division by two is integral. Changing representatives does not change the indicated residue. The omitted 8*2^k_i term in (1) is zero at every needed binary precision for sufficiently large k0.

* Choose the unique nonnegative delta_i with

      x_(i+1) = 3^a_i*(x_i+8)/2^(a_i+1+delta_i) in (4,8).   (8)

  Such a delta exists: before level scaling the value is >6, and dyadic seams cannot occur because x_i is irrational and remains irrational under the rational affine maps. This fixes D_(i+1).

Precision decreases by at least one per token, so this produces s<=b tokens. All the limiting x_i are strictly inside their respective bands. By continuity of the finitely many inverse affine maps in (8), there is a nonempty open interval J_s about x_s, with compact closure inside (4,8), whose inverse images remain in the bands and whose initial inverse image lies inside I.

Next enforce all the odd divisibilities needed to realize this limiting prefix as genuine integer reset edges. Put A_i=sum_{j<i} a_j and Q_i=Q*3^A_i. Refine the k0 progression once more to fix k0 modulo Q_s and phi(Q_s) (compatible with its previous class by choosing any representative extending that class). This fixes each k_i and each 2^k_i modulo every Q_i. Choose X0=2*r+5 (mod Q). Define recursively

    X_(i+1) = 2^(-a_i-1)*3^a_i*(X_i+16*2^k_i+2*k_i+5)
                     (mod Q_(i+1)),                    (9)

where the inverse power of two exists since the modulus is odd. The new residue is well-defined from X_i modulo Q_i because Q_(i+1)=3^a_i*Q_i. Modulus 1 imposes no condition.

Apply Section 3 to the final level class k_s=k0+D_s, the interval J_s, and the odd height residue h_s=(X_s-5)/2 (mod Q_s). It supplies arbitrarily large exact h_s,k_s with one true reset edge to F_n. Now define all earlier centered heights backwards by

    2*h_i+5 = 2^(a_i+1)*(2*h_(i+1)+5)/3^a_i
                    -16*2^k_i-2*k_i-5.                (10)

Equation (9) ensures the division by 3^a_i is exact, and the recovered centered height has residue X_i modulo Q_i. It is odd because the first term is even and the subtracted expression is odd. Thus all h_i are integers. The exact normalized relation differs from (8) only by terms tending uniformly to zero as k0 tends to infinity, since all tokens, shifts, and affine coefficients are fixed. Explicitly the forward correction is

    (3^a_i/2^(a_i+1) + k_(i+1) + 3/2) / 2^k_(i+1).

Its finite inverse composition also tends to zero. The compact margin chosen for J_s ensures that, for sufficiently large k0, every h_i is positive and every strict source band holds, with x_0 in I. Therefore (10) gives genuine ResetParent edges by (1).

Finally the required binary residues follow by backward induction. At step i with a_i<l_i, the residue of 2*h_(i+1)+5 modulo 2^(l_i-a_i) is fixed by h_(i+1) modulo 2^l_(i+1). Equation (2) divides only by the odd number 3^a_i, then multiplies by 2^a_i; it therefore recovers exactly r_i modulo 2^l_i, by the construction of r_(i+1). This includes l_(i+1)=0, where oddness alone fixes the last digit. If a_i=l_i, the first term of (2) is automatically zero modulo 2^l_i, recovering the prescribed zero-valuation cylinder. Hence h0=r (mod 2^b) and, from (9), h0=r (mod Q), so h0=r (mod m).

There are s<=b prefix edges followed by one direct fatal edge. All k0 can be chosen above any bound. This proves the theorem, with n>=50001 obtained simply by taking the final progression sufficiently far.

## 5. Consequence for finite abstract safety invariants

A set of reset heights is safe if it excludes every F_n and is forward closed under the exact ResetParent relation. Any member with a finite ResetParent chain to F_n contradicts safety.

Consider a predicate on the valid (h,k) pairs defined using finitely many fixed congruences in h,k, finitely many comparisons of x=(h+k+4)/2^k with real constants, and arbitrary exceptions below some bounded k. After combining moduli and partitioning (4,8) at those constants, the tail predicate is constant on each open interval/residue cell. If it includes even one such cell, the theorem supplies an exact fatal-reaching member. Thus a safe set of this form, above its finite exceptional levels, can contain only points on finitely many exact normalized-height boundaries.

An infinite valid reset trajectory cannot stay on finitely many such boundaries. Its heights strictly increase by [ResetParentStrict.lean](ResetParentStrict.lean), so its sweep levels are unbounded. An exact boundary value x occurring at integer h,k must be dyadic rational. Above all their fixed dyadic denominator exponents, h+k+4=x*2^k is even, so the only possible next reset is a=0. Its successor u has the same level k for all sufficiently large k, because

    (u+k+4)/2^k = 4+x/2+(k+2)/2^k

lies strictly between 4 and 8, with margin. This value is strictly above 4+x/2 and approaches it. For a finite set of boundary values, the positive distances from any 4+x/2 to a boundary greater than it have a positive minimum (or no such boundary exists). The correction eventually lies below all of these distances. Thus the successor is not a boundary. Contradiction.

Accordingly no such finite modular/interval invariant can certify an infinite authentic blank-root reset orbit. If the blank-root machine halts, no safe invariant containing it exists anyway. This is a restriction on a proof methodology, not a classification of that orbit. It does not apply to a language of physical tapes recognized by a general automaton unless that language is proved to reduce to this finite-cylinder class. The independent FAR search should continue.

## 6. Evidence and next mathematical question

The finite reproducer verifies the ascending-prime selector for all 2,800 target residues over ten composite/prime-power moduli and checks explicit full-grammar prepared chains, including a two-edge chain with h=7 (mod 10) and another with h=17 (mod 20). These are examples, not the proof of density. The unbounded theorem rests on Sections 2–5, including the irrational-rotation and finite-prefix arguments. The proof has not been ported to Lean; no source CI run was launched.

The substantive next question is what **growing-precision, nonlocal relation between the low binary/ternary digits and the normalized height** separates the authentic blank orbit from the fatal-reaching prepared states. Increasing a fixed modulus or making a finite partition finer cannot remove the obstruction. A useful positive approach must use an abstraction outside this class, or exploit information about the authentic root that is lost in every such fixed cylinder. The exact rooted cutoff remains 50,000; the machine and BB(6) are unresolved.
