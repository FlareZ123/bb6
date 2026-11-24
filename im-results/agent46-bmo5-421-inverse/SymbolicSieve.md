# BMO5 terminal ancestry: exact geometric residue tree and compressed sieve

**Paper theorem (not yet kernel-certified):** for each depth t≥0, the set of terminal indices i≥4t+10 having at least t defined inverse steps is exactly a union of 2^(t+1) distinct residue classes modulo 2·3^t. Its natural density is (2/3)^t. Every fixed depth has infinitely many survivors.

**Finite computation:** all 0≤i≤10^12 classified; no ancestry root in {1,2,3}, no unresolved cases. This concerns the shared BMO5 section reduction for #252/#421/#754. Neither the unbounded terminal existential nor BB(6) is decided.

## Exact symbolic recurrence

Let P_k=5·2^k. By CapInverse.lean a regular inverse from y to band k has 3x=y+2P_k-3k-12, exists iff P_k+3≤y≤4P_k-9 and y≡P_k (mod 3). Special images are 2P_k and the exceptional image is 5.

Write the depth-s target as D y=A P_(i-d)-B i-C, D=3^s. Start (A,D,d,B,C)=(2,1,0,1,6) at T_i=10·2^i-i-6. Choice e=0 or 1 selects band k=i-d-e. The exact child parameters are d'=d+e, D'=3D, A'=2^e A+2D, B'=B+D', C'=C+D'(4-d').

Inductively D<A≤2D, d≤s, B=(3D-1)/2. With E=(Bi+C)/D, E'=E/3+i-d'+4. Thus for i≥4t+10 and s≤t, 9≤E≤2i+6: base E=i+6; step i-d'≥i-t≥10 and E/3+i+4≤2i+6.

The inequality 5·2^(i-t)>(2i+9)·3^t holds when i≥4t+10. At i=4t+10 induct on t (LHS multiplies by 8, RHS by 3(8t+37)/(8t+29)<4); each increment of i doubles LHS and adds 2·3^t to RHS. Therefore P_(i-d)/D>2i+9. Every integral symbolic target satisfies P_(i-d)+3<y≤2P_(i-d)-9, using A≥D+1 and A≤2D. In particular j=log2(floor(y/5))=i-d. No special inverse applies; only j and j-1 can be regular parents. Both have the required interval inequalities. Their residues P_j and P_(j-1) modulo 3 are the two nonzero classes, hence no predecessor iff y≡0 mod 3; otherwise the unique authentic predecessor is the corresponding child. This proves the recurrence for every prefix within the stated guard.

## Exact residue lifting

Fix a surviving depth-s residue r modulo M=2D and its symbolic state. The child numerator F(i)=A'·5·2^(i-d')-B'i-C' is divisible by D throughout this class, by substitution of the parent equation. Since 2^(2·3^s)≡1 mod 3^(s+1) (induct by cubing), increasing i by M leaves the exponential term unchanged modulo 3D. B'≡1 mod 3; hence the three lifts r,r+M,r+2M have numerator residues separated by D modulo 3D. Exactly one is divisible by D'=3D. The two child lifts cannot coincide, since a common sufficiently large representative would require both y≡P_j and y≡P_(j-1) mod 3.

For representatives smaller than d', interpret negative powers of 2 by modular inversion modulo the odd modulus, or use any sufficiently large representative. The two starting parity classes cover all i. Induction yields exactly 2^(t+1) distinct classes at depth t modulo 2·3^t, valid beyond 4t+10, establishing the density and the fixed-depth obstruction.

## Reproduction

symbolic.py checks the recurrence and residue distinctness through depth 10 against literal inverses for indices below 5000. sieve.cpp counts interval members in the two child classes, excluding all other lifts at the current depth (their root is divisible by 3 and larger than 3). Singleton classes continue without materializing the counter; small indices 0..511 use literal arbitrary-precision inverse. Fast path carries P modulo 3^39 with 64/128-bit integers and switches to Boost cpp_int at deeper levels. For N≤10^12, A≤2·3^39<2^64; products with i fit signed 128-bit and modular products fit unsigned 128-bit. Cutoffs report unresolved and exit nonzero.

Run: g++ -O3 -std=c++17 -Wall -Wextra sieve.cpp -o sieve && ./sieve 1000000000000

Local 24 Nov run: 8.96 seconds, peak 1540 KB, 118803816 nodes, 42169065 singleton continuations, 136296 deep continuations, maximum inverse depth 73, classified 1000000000001, unresolved 0, rootHits 0. Literal independent histogram matched C++ exactly for 0..5000. Expected blobs: C++ e2e02c666fd7a1c89cd771c813a32b0271e7403b, Python 73cac32744a697bad458286cda2271a438d75d43.

The unbounded quantifier remains. Each fixed depth has survivors; the moving index/depth constraint and eventual small-root ancestry need a proof. Kernel verification and independent novelty review remain open.
