# Machine C: prepared halting rays in every congruence cone; no semilinear safety invariant

**Agent 12, 24 November 2026.** This is a constructive, unbounded result for the exact section map, independent of the blank root. The finite affine-line obstruction uses [complete-itinerary aperiodicity](2026-11-24-machine-c-aperiodic-section-itinerary-agent12.md). The modular steering identities are checked in [ModularSteering.lean](../im-results/agent12-c-high-shadow/ModularSteering.lean), Lean 4.36.0-rc2, with standard axioms only. The finite-group, Diophantine lifting and semilinear synthesis arguments below are mathematical paper proofs, not an end-to-end Lean theorem. [halting_ray.py](../im-results/agent12-c-high-shadow/halting_ray.py) is a constructive exact-integer implementation with coefficientwise guard checks.

## Theorems

1. For every positive integer N, every residue class (a0,k0) mod N, and every open subinterval I of (0,1), there is an infinite integer arithmetic ray of prepared section states (a,k), lying in that class with a/(a+2k) in I, all of which reach an immediate terminal state after the same finite ordinary branch word. In particular there are arbitrarily large prepared halting states in every congruence cone.
2. No infinite successful section orbit is eventually contained in a finite union of affine lines in the counter plane.
3. No nonempty semilinear subset of the section counter plane is both forward-closed and terminal-free. In particular no Presburger-definable inductive nonhalting invariant exists in these two section counters.

None of these statements decides the blank orbit. The first concerns prepared states, not blank reachability.

## 1. Exact ordinary affine maps and branch geometry

Use A=a,M=a+2k, so A and M have the same parity and 0<=A<=M. Write o=M mod 2. For an ordinary branch of shift r>=1 the equations from the aperiodicity proof are

    M'=M+3r+1,
    A'=2^r A-M+b_r(o),
    b_r(o)=2^r(2+o)-(3r+1)-2o.

For r=1 this is direct (b_1=0); for r>=2 it is a regular-input bounce with exactly r-2 recursive calls and ordinary exit. Source definitions: [FastSectionDef.lean](../im-results/agent46-c-jump/FastSectionDef.lean), [BounceCalc.lean](../im-results/agent46-c-jump/BounceCalc.lean).

At large mass, a prescribed r is realized on any affine integer ray with limiting slope s=A/M strictly in (2^-r,2^(1-r)). For r=1 the direct guard holds by s>1/2. For r>=2, K=a-1 and c=M-2A+3. At recursive depth i the leading terms are K_i ~ 2^i s M and c_i ~ (1-2^(i+1)s)M, using c+2K increase by 3 at each recursion. For i<r-2 the recursive guard c_i>2K_i+6 or +8 holds strictly at leading order; at i=r-2, c_i grows positively and is strictly below the ordinary exit upper bound at leading order. Thus c_i=4,5 and all small-input exceptions are absent for sufficiently large ray parameter.

The output limiting slope is f_r(s)=2^r s-1 in (0,1). The inverse slope map is g_r(s)=(1+s)/2^r. For any finite word, composing inverse slopes gives an open interval (Q/P,(Q+1)/P), where P=2^R and Q is the odd integer with one-bits at its suffix shift sums. Conversely any odd Q with 0<Q<P is such a word: the successive cyclic gaps between its one-bits are the reversed shifts. Such dyadic open intervals form a basis for interior intervals in the sense that any given open I contains one of them. Choose such a prefix word. Any appended word ending at slope strictly between 0 and 1 has its full inverse slope inside the prefix interval. Hence arbitrary further modular steering is compatible with the desired initial open cone.

## 2. Finite modular controllability

For a modulus L=2N write L=2^v d with d odd and v>=1. Project the ordinary affine equations to states

    (A mod d, M mod L).

Parity is well-defined by the second coordinate. The shifts r=1,2,3 give permutations of this finite state space: M' determines M and parity, and 2^r is invertible modulo odd d. Their inverse permutations are therefore positive powers, and any word in the generated group can be represented by a finite positive word of shifts.

Denote the direct permutation by D. Two useful parity-preserving permutations are F=B_3 and G=B_2^2, where B_r is the ordinary shift-r map. On fixed parity o, their integer affine lifts are

    D(A,M) = (2A-M,M+4)
    F(A,M) = (8A-M+6+6o,M+10)
    G(A,M) = (16A-5M+6o,M+14).

For any parity-preserving affine map H(A,M)=(P A-Q M+C,M+w) with P a power of 2, the commutator K=D H D^-1 H^-1 on the projected space is the shear

    K(A,M)=(A+g M+h_o,M),    g=P-Q-1,
    h_o=C-w+4Q-g(w+4).

This follows by comparing D H to K H D; no inverse over integers is required. The next commutator-like product D K D^-1 K^-2 is the constant translation (A,M)->(A-8g,M): compare D K to translate(-8g) K^2 D. These integer polynomial identities are checked in ModularSteering.lean.

For F, g=6 gives translation -48; for G, g=10 gives -80. Their composition with inverses yields translation -16 (twice -48 plus 80), a unit modulo every odd d. Hence at any fixed M residue, all A residues mod d can be reached by positive shift words. Separately, D and F change M by 4 and 10, generating all even changes mod L; B_2 changes M by 7 and flips parity. Therefore the projected action is transitive.

This is exact modular controllability, not a density or random-walk heuristic. It also gives an elementary terminating search algorithm: breadth-first search over at most dL projected states using shifts 1,2,3 finds any specified target set of projected residues. The abstract group argument justifies its termination without a modulus cutoff.

## 3. Steer to the high terminal family and lift exactly

Fix m>=0 so T=2^(2m+2) is divisible by 2^v, and write D0=6m+7. The high terminal family is

    A odd, A>=3, M=T(A+3)-D0.

For all sufficiently large A this is an actual terminal section state, directly from the source. Start with K=A-1 even, c=M-2A+3. After i recursive calls K_i+4=2^i(A+3) and c_i=M+9+3i-2^(i+1)(A+3). At n=2m+1, c_n=5, the even-middle terminal case. At i=n-1 the recursive guard c_i-(2K_i+8)=2; at earlier depths it is positive for large A because its leading coefficient is positive. Also a>=2,k>=1,a<2k at large A. Thus this family truly halts; it is not only a necessary halting condition.

Choose an initial lift A0=a0, M0=a0+2k0 mod L. Apply the prescribed prefix word to its projected state. By transitivity append a finite word steering to projected residues satisfying

    M'=-D0 mod 2^v,
    M'=T(A'+3)-D0 mod d.

The first implies M' is odd, and since T divisible by 2^v these are exactly the high terminal line equation modulo L. The second is solvable for A' mod d because T is invertible there. Actual A' parity equals M' parity by the ordinary formulas.

For the entire word, compose the affine equations at the fixed initial parity:

    A'=P A-Q M+C, M'=M+W.

The target equation becomes

    TP A-(1+TQ) M=W+D0-T(C+3).              (3)

Its coefficients are coprime: TP is a power of 2 and 1+TQ odd. By the modular construction (3) holds modulo L for A0,M0. Substitute A=A0+Lx,M=M0+Ly and divide the residual equation by L. Bezout gives an integer solution, and all solutions include the ray with positive increments

    delta A=L(1+TQ), delta M=LTP.

The limiting slope is (Q+1/T)/P, exactly the inverse word slope of 1/T. It lies inside the chosen prefix interval I and every intermediate slope lies strictly inside its prescribed ordinary branch interval. For sufficiently large ray parameter every actual guard is therefore satisfied, and the final section state lies on the genuine high terminal family with large odd A'. Initial parity and both original counter residues hold because increments and residue modulus are multiples of 2N. The initial slope itself lies in I for every sufficiently large parameter. Discard the finite initial segment; the remaining ray proves Theorem 1.

The Python implementation explicitly solves (3) and computes the required ray-parameter threshold from every source guard as a linear integer inequality; it also checks the final c_n=5 identity coefficientwise. In 24 examples across eight moduli (including odd primes, powers of two, and mixed composite moduli), three narrow/wide separated slope intervals each yielded an infinite halting ray; 72 sample source-equation replays independently passed.

## 4. No finite union of affine lines supports an infinite orbit

Suppose an infinite orbit eventually lies in finitely many affine lines in (M,A). Discard constant-M lines, lines with slope outside [0,1], and finite intersections of distinct lines, since M grows strictly and these contribute only finitely many valid points. Each remaining line is A=sM+b. Call s=0 lines horizontal; they have fixed A.

For s>0 and fixed parity, the complete branch label is deterministic for all sufficiently large M on that line whenever the edge is successful. Indeed A>=2,k>=1 eventually along the orbit (k=0 impossible after the first successful edge). If direct does not apply, the initial K=A-1 grows linearly in M while c<=M+3; each recursive call decreases c by at least 2K, bounding the recursive depth uniformly. Every guard at each of the finitely many possible depths is an affine inequality/equality in M on the line at fixed parity, so its truth eventually stabilizes. This also covers limiting branch boundaries and the exceptional c=4 exit.

The affine edge maps such a line to another affine line and changes M by a fixed positive constant, with deterministic parity update. If the successor lies in the prescribed finite union infinitely far out, its line must coincide with a unique line of the union: otherwise all intersections are finite and can be discarded uniformly. Thus positive-line/parity states have deterministic successor line and parity on the tail, and bounded mass increments. If the orbit stays among positive lines indefinitely it is eventually periodic in complete labels, contradicting the aperiodicity theorem. Also no positive-line/parity state can repeat between consecutive horizontal visits, since deterministic successors would then force an endless positive-line cycle. Hence there are infinitely many horizontal visits, and the number of positive-line edges between them is uniformly bounded.

For fixed horizontal A and large M, a bounce has fixed initial middle K (1 if A=0, 4 if A=1, otherwise A-1) and c+2K=M+c0 with fixed integer c0. At depth n let B=K+3 for odd K, K+4 for even K. The exit formulas give

    M'=M+3n+w0,
    A'=2^(n+2) B-M'-2delta,

with w0 fixed by the input line and exit type, and delta in {0,1,3} for odd ordinary, even ordinary, even exceptional respectively. If A'=s'M'+b' lies on any of the finitely many successor lines, then

    (1+s')M'=2^(n+2)B-2delta-b'.             (4)

Thus for each horizontal source, successor line and exit type, the possible source masses form a sequence M=c1*2^n-3n+c2 with c1>0 and fixed real constants. For M<=X, (4) implies n=O(log X) once M is sufficiently large (M grows exponentially in n); each such n supplies at most one M. There are only finitely many source/target/exit choices. Hence at most O(log X) horizontal-visit masses are possible up to X, and each horizontal edge increases mass by O(log M).

Let m_i be the masses of consecutive horizontal visits on the orbit tail. Bounded positive-line paths and the preceding estimates imply m_{i+1}-m_i<=C(1+log m_i) for a fixed C. Also i<=C'(1+log m_i), because the horizontal masses are strictly increasing and drawn from the finite union in (4). Summing the gap bound yields m_i<=m_0+O((1+log m_i)^2), impossible as m_i tends to infinity. Contradiction. This proves Theorem 2.

## 5. Semilinear obstruction

A semilinear set in N^2 is a finite union of sets b+sum_i N v_i. If a component has two linearly independent generators u,v, its subcomponent b+N u+N v contains every sufficiently large point of the lattice b+Z u+Z v in any closed interior subcone between u and v. Indeed the real generator coefficients are positive for sufficiently large such points and integral by lattice membership. This lattice contains the congruence class b modulo N=|det(u,v)|, by the adjugate identity. The interior cone contains a nonempty open range of ratios a/(a+2k) strictly between 0 and 1. Choose a strictly smaller ratio interval there. Theorem 1 constructs an infinite ray of prepared halting states in this congruence class and interval; all sufficiently large members belong to the subcomponent. Therefore a terminal-free forward-closed set cannot contain a rank-two component, because these states have a finite path to an immediate terminal state.

All remaining components have rank at most one, hence lie in a finite union of affine lines and points. Any nonempty forward-closed terminal-free set supplies an infinite successful orbit, contrary to Theorem 2. QED.

Presburger-definable subsets of N^2 are semilinear, so this also excludes nonempty Presburger safety invariants in these section counters. It does not exclude non-semilinear invariants, invariants in richer configuration representations, or direct halting proofs. The existence of prepared halting rays in every congruence cone is compatible with a sparse authentic reachable set and with either blank-halting outcome.
