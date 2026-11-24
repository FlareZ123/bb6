# All-depth compact affine terminal inverse

For shifted Space Needle counter b=d_original+2, the blank root is b=3 and the terminal targets are b=2^K, K>=2. For an incoming edge with w>=0 write m=w+1, D=2^m+3. Its source is p=2^(m-1)(2q+3), q>=0, and the exact parent equation is 2b+5-2m=D(2q+3).

## All-depth theorem

Represent a reverse node as 2Lb=2^n+d, where n>=1, L>0 odd, d even. The terminal representation is (n,L,d)=(K+1,1,0). Every legal inverse step transforms it by

    C=d+L(5-2m)
    n'=n+m
    L'=LD
    d'=2^m C.

The necessary and sufficient test is LD | (2^n+C), with quotient >=3 and odd. The odd condition is automatic for the indicated invariant. All inverse nodes are strictly smaller than their targets. In addition the normalized affine correction satisfies d<2L at every depth: for m>=1, 2^m(5-2m)<=6, and multiplying the previous strict bound gives d'<2LD.

Choose H>=1 with |C|<2^H. Every predecessor satisfies one of:

* ordinary: m < H+2 floor(n/m)+2 (hence m^2 < (H+2)m+2n);
* cancellation: m divides n and C=-(-3)^(n/m).

To prove this, set k=floor(n/m), t=n mod m. The first residue is (-3)^k 2^t+C modulo D. If m>=H+2k+2 and t<=H, the absolute value is <D and the residue must vanish. Since C is odd, t=0. If t>H, multiply by 2^(m-t) to obtain (-3)^(k+1)+C2^(m-t); it is odd and its absolute value is <D, a contradiction.

For m>=4, C<0 by d<2L, so a cancellation has even k=n/m>0. There is at most one such m: as m increases through divisors of n, |C| increases strictly, whereas 3^(n/m) decreases strictly. Also k<H. The potential large exceptional m can therefore be computed without factoring n. Solve k(d+5L+3^k)=2Ln for even k in [2,H-1] with m=n/k above the ordinary cutoff. The left side is strictly increasing once positive; comparison to the positive RHS is monotone even when it begins negative. Binary search, verify equality and n mod k=0, then perform the exact LD-divisibility/positivity test. No extra large cancellation candidate is possible.

All of the algebra, rotation dichotomy, positivity/odd-quotient equivalence, invariant preservation, uniqueness and exponent bound are locally kernel-checked in TerminalAffineRotation.lean with Lean 4.36.0-rc2, using only propext, Classical.choice, Quot.sound. TerminalAffineRotationSource.lean imports the existing exact original machine reduction; local equation-interface smoke test passed, actual original-source CI acceptance pending. The source adapter also imports the strengthened cancellation cutoff of SharpenedRotationBound.md.

## Exact compact executable

terminal_affine_solver.cpp performs a complete reverse DFS from any fixed terminal exponent K in its supported unsigned-long range. It never explicitly constructs 2^n or a full node counter in the main solver. It uses uniform H=bitlength(|d|+L(2K+5)), exact modular exponentiation mod LD, bitlength comparison for the positive quotient condition, and the above unique-exception search. Every m is physically <K because 2^m<b<=2^K. The root test compares 6L-d against a power of two. No heuristic pruning or arbitrary bit limit is used; an explicitly supplied node budget reports INCOMPLETE if exhausted. Exponent overflow is an error, never an exclusion. Coefficient sizes can still grow with history, and no bound uniform in K is asserted.

Compile:
    g++ -O3 -std=c++17 terminal_affine_solver.cpp -lgmpxx -lgmp -o terminal_affine_solver

Small regression (all reverse trees K=2..16) compared each node against materialized exact inverse equations, including predecessor values and monotone decrease; passed. Main solver results:
    K=100        4 nodes, 3 edges, 1 leaf, excluded
    K=1000       5 nodes, 4 edges, 1 leaf, excluded
    K=10000      6 nodes, 5 edges, 1 leaf, excluded
    K=100000     7 nodes, 6 edges, 1 leaf, excluded
    K=1000000    8 nodes, 7 edges, 1 leaf, excluded
    K=10000000   9 nodes, 8 edges, 1 leaf, excluded
    K=100000000 10 nodes, 9 edges, 1 leaf, excluded (22.51s locally)

These are finite exact arithmetic exclusions via the established original-source inverse correspondence, not formal finite Lean certificates and not an all-K nonhalting proof. The all-depth theorem addresses the regular sector as well as the cancellation sector; its per-node ordinary count is O(H+sqrt(n)), plus at most one exceptional m>=4. This is a genuine generalization of the terminal-only quadratic feeder lists and the earlier cancellation-specific affine audit. No total worst-case DFS complexity improvement is claimed.

Next: exploit the coefficient-size dependence and normalized correction to control the all-depth root-reaching word uniformly. Avoid scanning more arbitrary exponents merely to produce larger finite numbers.
