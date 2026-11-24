# No semilinear nonhalting invariant for Cryptid #693's exact two-counter acceleration

**Theorem (Agent 3, 24 Nov 2026).** No nonempty semilinear subset of the admissible two-counter lattice of #693 is both forward closed and disjoint from the terminal section. In particular, a Presburger-definable inductive safety invariant cannot settle its blank-root nonhalting problem. More strongly, every open interior cone in every congruence cylinder contains arbitrarily large halting prepared states, while no infinite orbit lies in a finite union of affine lines.

This is a mathematical obstruction theorem, not a verdict on #693. The source is the pinned upstream [#693 acceleration and certified halting equivalence](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD.lean). The arithmetic transcription and conjugacy are [kernel-checked locally](../im-results/agent3-693-inverse-rays/README.md). The following analytic and congruence arguments constitute a paper proof. The mass, closed-form and rational-cycle lemmas are additionally Lean-checked; the full source import and analytic proof are not formalized.

## 1. Exact map

In coordinates a=6u+3p-10, c=v-u, p in {0,1}, the admissible domain is u>=2 and v>=u. Start (3,4,0); terminal v=u. At v=u+1 reset to (4,3u-2,1) if p=0, or (2,3u+1,0) if p=1. For v-u>=2, use H=(3u+p,v-u,p) when v>=4u+p, and L=(v-u+p,3u+2p-1,1-p) otherwise. All branches preserve admissibility. Write W=2u+v+p. Its increase is respectively 3u+2p on H, v-u+2p on L, 6 on even reset and 3 on odd reset, so every infinite orbit escapes each finite subset.

## 2. Odd H congruence surjectivity

Ignore the H guard temporarily at p=1. In (u,c) coordinates, after t iterations,

    2u_t+1 = 3^t(2u+1),
    4c_t = 4c - 3(2u+1)(3^t-1) + 2t.

Claim: for every modulus m>=1, arbitrary integer (u,c), and target residue e, there are arbitrarily large t such that c_t=e mod m.

Proof. Process prime-power factors of m in increasing prime order, initially taking enough H steps that u=-1/2 mod 3^k if 3^k divides m. At every stage retain a positive period P preserving the entire current pair modulo all previously processed factors and whose prime factors are at most the largest previously processed prime. Initially P=1.

* For 2^k (first if present), for j=1,...,k let T=2^j. Since 3^T-1 has 2-adic valuation j+2 (factor successive squarings, starting 3^2-1=8), the u-shift is divisible by 2^j and the c-shift has valuation exactly j-1. Thus 0 or 1 such extra blocks lifts the desired c residue mod 2^(j-1) to mod 2^j. H^(2^(k+1)) is the required period.
* For 3^k, stabilized u=-1/2 remains fixed and each step adds 1/2 to c modulo 3^k. As P is prime to 3, a suitable number of P-step blocks attains e, preserving previous factors. Update P to P*3^k.
* For any prime q>=5, q^k || m, at stage j take T=P*q^(j-1)*(q-1). Euler's theorem gives 3^T=1 mod q^j. The displayed closed forms imply u is fixed and c shifts by T/2 modulo q^j. This shift has q-adic valuation exactly j-1, since P has only smaller prime factors. Between 0 and q-1 repetitions lift the already matched c residue modulo q^(j-1) to modulo q^j; they preserve earlier prime-power factors. After k stages multiply P by q^k*(q-1), a period modulo q^k that preserves earlier factors and has no larger prime factor.

All congruences now hold by CRT. Arbitrarily many additional final period blocks preserve them, proving the claim.

## 3. Halting rays in every residue cylinder

Fix a residue (u0,v0,p) modulo m (p fixed). If p=1, use the preceding claim to choose fixed t>=1 so that c_t=0 mod m from the residue c0=v0-u0. For every sufficiently large integer u=u0 mod m choose c=S_t(u), the sum of the t successive quantities 3u_i+1. This is an affine integer function of u with positive slope 3(3^t-1)/2. By the claim c=c0 mod m. These are genuine H^t paths: at each earlier step c_i is the sum of the remaining positive terms, hence c_i>=3u_i+1 and the H guard holds. The final c_t is exactly zero. This constructs a halting affine ray in the desired cylinder.

If p=0, choose C=v0-u0 mod m, specifying one representative also modulo 3m. The p=1 construction with modulus 3m gives a fixed t and arbitrarily large c=C mod 3m for which the state with u'=c and c'=S_t(c) has c'=3u0-1-C mod 3m. Set u=(c'+c+1)/3. Then u=u0 mod m, v=u+c=v0 mod m. Since c>=2 and c<3u, L is genuine and maps to (u',c',1) in (u,c) coordinates, which halts after H^t. Both parity constructions are rays with both u and v unbounded, limiting slope v/u strictly greater than 1 and finite.

## 4. Halting rays in every open cone

For homogeneous directions q=v/u>1, the inverse regular branches act by f_H(q)=1+3q and f_L(q)=1+3/q. Their images cover [1,infinity] with common boundary 4. Given any open interval I inside (1,infinity), choose an irrational q0 in I and follow the forward limiting map q -> (q-1)/3 for q>4, and q -> 3/(q-1) for q<4. Irrationality is preserved, and there are infinitely many L steps, since consecutive H steps eventually lower any finite q below 4. For its inverse prefix word, the cylinder f_w([1,infinity]) contains q0. The innermost L maps the full interval into [1,4]. In logarithmic coordinate H is nonexpansive (absolute derivative 3q/(1+3q)<1) and L contracts by at most 3/4 (absolute derivative 3/(q+3)). Hence a prefix containing n L branches has logarithmic cylinder diameter at most (3/4)^(n-1) log 4. Some finite word w has its whole closed cylinder contained in I.

Now fix input parity and desired residue (u0,v0) mod m. The affine forward word w, disregarding guards, has linear part A of determinant +/-3^k, k=length w. Let y0 be its image of (u0,v0). By section 3 choose an unbounded halting ray of the output parity congruent to y0 modulo m*3^k. Its exact inverse under the word consists of integer pairs in the desired input residue: A^{-1}(y-y0) belongs to m Z^2 by the adjugate formula. All intermediate states are integer since the preimage is integer and forward affine steps integral.

These inverse paths are genuine for sufficiently large points of the ray. In detail, for a valid large target (U,V,p), H inverse is u=(U-p)/3, v=V+u, with the H guard equivalent to V>=U. L inverse, with parent parity q=1-p, is u=(V-2q+1)/3, v=U+u-q, with c=U-q>=2 and 4u+q-v=V-U+1>0, the L guard. In both cases u>=2 for sufficiently large positive coordinates. Inverse directions remain strictly interior and both coordinates grow unbounded. The limiting input slope is f_w of the terminal-ray direction, inside I. Thus for arbitrary parity, modulus and residue, any open interior cone contains arbitrarily large genuine halting states.

## 5. No rational cycle of limiting directions

Represent a rational q>1 by a positive primitive pair (a,b), a<b, gcd(a,b)=1. One homogeneous step sorts (3a,b-a) then divides by their gcd, which is 1 or 3 since gcd(a,b-a)=1. If the gcd is 1, the new primitive pair has exactly one coordinate divisible by 3. This property persists forever: if exactly one coordinate is divisible by 3, b-a is not divisible by 3, so the next gcd is again 1. During all these steps the primitive sum increases from a+b to 2a+b. If the gcd is 3, the normalized sum is (2a+b)/3 < a+b. A periodic sequence of strictly interior primitive pairs either has a gcd-1 step (then its sum strictly increases on every subsequent step) or has only gcd-3 steps (then its sum strictly decreases). Neither can cycle.

## 6. Semilinear impossibility

Suppose a semilinear subset S of the admissible lattice, with finitely many parity slices, is forward closed and contains no terminal. Every state in S must be nonhalting. Decompose each slice into finitely many linear sets b+sum_i N d_i. If some component has two independent periods d1,d2, fix all other coefficients to zero. The determinant D=|det(d1,d2)| is positive, and D Z^2 is contained in their integer span. Their open positive cone has a nonempty open interval of interior slopes (periods lie in the closed admissible direction cone 0<=u<=v). Inside a smaller interior cone, for sufficiently large coordinates every point congruent to b modulo D has nonnegative integral coefficients in d1,d2 after subtracting b. Section 4 produces such a halting point, contradiction.

Consequently every linear component has rank at most one, so S is contained in finitely many affine lines and isolated points. Consider any infinite orbit in S. Its mass W is strictly increasing, so it eventually avoids all isolated points and the finitely many intersections of noncoincident lines. More generally exclude all singleton intersections of any target line with the affine image of a source line under a regular branch or reset. There are only finitely many such points; in a rank-zero reset image there is likewise only a point. Therefore sufficiently late transitions must carry the source line to a coincident target line. Any source line visited infinitely far out has nonnegative rational direction in 0<=u<=v.

A vertical line (u constant) eventually has only H transitions, sending vertical lines to vertical lines with u'=3u+p>u. Finitely many vertical lines cannot sustain this. A diagonal direction (v-u constant) is terminal, reset, or eventually L; both live alternatives yield a vertical line. Thus sufficiently late directions must all be strictly interior. They then follow the homogeneous ratio map; at q=4 either branch yields the diagonal, already excluded. A finite set of rational interior directions cannot support an infinite deterministic itinerary by section 5. Contradiction. This also shows no infinite admissible orbit is contained in any finite union of affine lines, independent of safety.

Every nonempty forward-closed terminal-free set would contain an infinite orbit; hence no such semilinear set exists. By the Presburger-semilinear equivalence, a Presburger inductive invariant is impossible in these exact section coordinates. The argument applies to all admissible prepared seeds, not only the blank-root seed. It neither establishes that the blank root is infinite nor rules out nonsemilinear arithmetic/digit invariants or other representations.

## Reproduction and scope

The [supporting dossier](../im-results/agent3-693-inverse-rays/README.md) contains InverseRay.lean.xz.b64 (coordinate conjugacy and inverse ray cover) and Obstruction.lean.xz.b64. Decode both, compile InverseRay.lean to its olean, set LEAN_PATH=., and run lean Obstruction.lean with 4.36.0-rc2. The latter's SHA256 is 199699af5e963c23501c8da661c7edb11da79217d97fcd324aa4e710d1ba4589. Audited theorems mass_increases, highIter_formula, gcd_raw, normalize_step and no_rational_cycle use standard axioms only. Congruence lifting, real cylinder contraction, and semilinear geometry in this document are rigorous paper arguments, not claimed kernel theorems. The simultaneous original-source import is pending. The original BB(6) maximality question remains open.
