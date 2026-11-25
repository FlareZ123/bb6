# F119: no ultimately periodic section safety invariant

**Theorem (paper proof).** For every integer modulus m>=1 the directed congruence graph of the generic tag-1 F119 section edges is strongly connected. In fact a finite, explicitly specified subset of the valuation branches suffices. Consequently an eventually periodic subset of tag-1 section coordinates that is unbounded and closed under the generic transitions must contain every sufficiently large integer. No terminal-free forward-closed section invariant containing the authentic blank section (4,1) can be ultimately periodic separately in each tag.

This is a method obstruction, not a halt/nonhalt decision. It applies to the source-accepted F119 recurrence in [README.md](README.md), not to arbitrary abstractions that retain nonperiodic history. The arithmetic identities and binary-digit lifting lemma in F119ModularCore.lean are kernel checked locally with Lean 4.36.0-rc2; the full graph/CRT proof below is paper level.

## Exact graph

Put p=3^h. For h>=0, r=1 or 2 and t>=1, a generic tag-1 edge has

    x = p(3t+r)
    y = (3p+1)t + pr + h + 3 + [r=2].

Taking t>=1 is enough; it excludes the pure-power case and ensures x>=4. For a fixed m, every t residue can be realized by arbitrarily large positive t. Thus modulo m an edge is precisely the pair given by these formulas for some t residue. The exact source recurrence includes all these edges. Write m=3^a N, N=2^b Q with gcd(Q,6)=1, and let l=ord_Q(3), with l=1 if Q=1. It suffices to use h in {0,...,a} union {2l-1}.

Let S be a nonempty subset of Z/mZ closed under these edges. We prove S is the whole ring.

## 1. Remove the 3-primary information

A cylinder at precision d<=a comprises all residues with x=z mod 3^d and x=B mod N, for fixed z,B. Initially S contains such a cylinder with d=a: this is one residue. Suppose d>0.

If z is nonzero mod 3^d, choose h=v_3(z)<d, and choose r in {1,2} from the unit digit of z/3^h modulo 3. Then x=3^h(3t+r) has the desired 3-primary residue exactly when t is a fixed residue modulo 3^(d-h-1). If z=0, choose h=d and either r; t is unrestricted on the 3-primary side. In either case, the condition x=B mod N fixes one residue of t modulo N, since 3 is invertible there. The Chinese remainder theorem gives all these t simultaneously, with arbitrary positive representatives.

As t varies under those conditions, y has one fixed residue B' modulo N. Since 3^(h+1)+1 is coprime to 3, the allowed y values cover an entire cylinder of precision d'=d-h-1 in the nonzero case, or d'=0 in the zero case. Thus that full cylinder is contained in S. In at most a steps a full 3-primary fiber over some B modulo N is contained in S.

Let U be the set of B modulo N for which that full fiber is in S. It is nonempty. For every fixed h and r under consideration, the affine map on N given by

    A_h = (3^(h+1)+1)/3^(h+1) mod N
    f_(h,1)(B) = A_h B + (3h+8)/3 mod N
    f_(h,2)(B) = A_h B + (3h+10)/3 mod N

preserves U. Divisions here mean multiplication by modular inverses. Indeed fix t modulo N to give x=B, then vary t freely modulo 3^a; the full input fiber accepts every such x, and y ranges over the entire output fiber because 3^(h+1)+1 is a 3-adic unit. The two affine identities follow by multiplication by 3^(h+1); see affine_one and affine_two in the Lean file.

## 2. Saturate the odd residues of N

Choose h=2l-1. The coefficient A_h is a unit modulo Q because 3^(h+1)=1 mod Q, hence A_h=2 mod Q. Modulo 2^b, A_h has exactly one factor of 2 when b>=2, since 3^(h+1)=1 mod 8 (h+1 even). For b=1 its residue is zero. The two constants are odd when b>=1 and differ by 2/3, which is twice a unit modulo 2^b.

The projection of U modulo Q is closed under both affine permutations f_1,f_2. A finite set closed under a permutation is also closed under its inverse. It is therefore closed under f_2 composed with f_1 inverse, the translation by 2/3. That translation generates all of Z/QZ, so the projection is the whole ring.

If b=0, this already proves U=Z/NZ. If b>=1, any word of length b in f_1,f_2 has output modulo 2^b independent of the starting value, because A_h^b=0 mod 2^b. Each output is odd. There is a length-b word giving each odd residue: fix its first map and vary its remaining b-1 maps. Two different words have different outputs, since the last differing map at distance j from the end contributes a difference of exact 2-adic valuation j+1, and all earlier differences have larger valuation. Here 0<=j<=b-2. Hence these 2^(b-1) outputs exhaust the odd residues. Equivalently this is the weighted binary-digit lemma digits_cover.

For any target odd residue modulo 2^b and any target residue modulo Q, choose such a suffix word giving the first target. On Q this fixed word is a permutation, so some element of U projects to the preimage of the second target. Applying the word gives both target residues. CRT now shows U contains every odd class modulo N.

## 3. Saturate the even residues

Use h=0. Its two maps satisfy 3y=4x+8 and 3y=4x+10 modulo N. They always give even y if b>0.

Prove by induction on d from 0 to b that the projection of U onto Z/(2^d Q) is full. The d=0 case was proved above. For d=1, any even target can be obtained from a suitable odd input: 4x=3y-8 mod 2 is automatic and determines one x residue modulo Q. For d>=2 and an even target y, choose constant 8 if y=0 mod 4 and constant 10 if y=2 mod 4. The equation 4x=3y-constant then specifies exactly one x residue modulo 2^(d-2), and exactly one modulo Q. By the induction hypothesis there is an x in U with these residues. Its image under the chosen h=0 map gives y at precision d. Odd targets were already present. This proves the induction and U=Z/NZ.

Together with the full-fiber definition of U, S=Z/mZ. Since the forward reachability set from any vertex is nonempty and closed, the finite graph is strongly connected.

## 4. Consequence for actual section invariants

Let I be a set of valid sections forward closed under every exact section Edge, containing (4,1), and disjoint from Terminal. Suppose the tag-1 coordinate set is ultimately periodic: for x>=T, membership is determined by x mod m. Totality of the exact section transition and strict growth force the infinite authentic orbit to be unbounded if I is safe. The source root invariant gives tag 2 only at isolated special sections, with a generic tag-1 successor; therefore infinitely many unbounded tag-1 coordinates lie in I. The corresponding residue set S is nonempty.

Every modular generic edge can be lifted with t arbitrarily large, so both its input and output exceed T. Its input belongs to I by eventual periodicity, and its output does by forward closure. Therefore S is closed under the exact congruence graph above and must be full. But all sufficiently large powers 3^(3k) with tag 1 are terminal (the exact power halt test is k'=0 mod 3 for exponent k'). Contradiction.

Thus even an arbitrary finite exceptional prefix followed by a union of residue classes cannot be a successful safety invariant. This rules out all semilinear one-dimensional tag-1 invariants, including arbitrary moduli and prime-power combinations; it does not rule out nonregular arithmetic conditions, finite automata on base digits, or invariants with extra history. Strong connectivity is an existential statement about modular representative changes at each edge, and cannot imply actual root halting.

## Evidence and use

- Lean arithmetic core: F119ModularCore.lean, with standard axioms only (propext, Classical.choice, Quot.sound). Its exported theorem digits_cover is general for any odd weights w_j at binary digit positions. The full CRT composition is not claimed kernel checked.
- Finite regression: python modular_check.py --limit 1024; all 1024 graphs strongly connected using only the stated finite subset of h, with 2,594,012 distinct directed edges summed across the graphs. This verifies small examples of the proof, not the universal quantifier.
- Closest previous F119 work: the two-parent gates and uniform affine inverse theorem here, and Agent32's inverse_fan.py. Neither established this obstruction. In particular, increasing a fixed residue modulus cannot close the actual blank-start theorem, and an inverse fan should use a genuinely history-dependent or nonperiodic inductive invariant instead of a residue-only cover.
