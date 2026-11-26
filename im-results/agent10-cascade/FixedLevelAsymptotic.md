# Exact all-index fixed-gap asymptotic for surviving #746 gates

**Status:** paper theorem over the original-source-certified exact ResetParent grammar. The new modular nonresonance lemmas in [SeamNonresonance.lean](SeamNonresonance.lean) have been checked locally on Lean 4.36.0-rc2 (only propext and Quot.sound). The full asymptotic and its source connection are not yet Lean-certified. This is not a blank-root decision.

## 1. Theorem

Write F(N)=4*2^N-N-4, and let A_g(N) be the number of distinct ResetParent ancestors of F(N), including itself, at levels N-g through N. Levels are defined by F(k)<=h<F(k+1). Fix g>=1. Along **every** sufficiently large surviving gate index N (N mod6 in {4,5}),

    A_g(N) = c_g N + O_g(log N),

where c_g is the explicit positive rational

    c_g = 1 + sum_w 1/(2*3^(A(w)-1)).

The finite sum is over all nonempty ideal inverse words w from normalized seam 8 whose first edge is odd, whose intermediate coordinates are all strictly between 4 and 8, and whose total level drop is at most g-1. An edge with valuation a and level drop delta acts by z -> C*z-8, C=2^(a+delta+1)/3^a. A(w) is its total valuation. The same-level edge has a=delta=0. Word counting is exact, not a sampling approximation. The list is computed by [ideal_seam_tree.py](ideal_seam_tree.py).

Per-level counts likewise have exact linear coefficients: level N itself contributes 1 vertex; the coefficient at level N-1 is 1; at level N-d, d>=2, the coefficient is the same sum restricted to total drop d-1. The O_g(log N) error is uniform in both surviving sectors, including indices arbitrarily close to dyadic seams. In particular there is no exceptional sparse sequence with a different leading coefficient.

For example c_1=1, c_2=4/3, c_3=73/54, c_4=79/54, c_6=19739/13122, c_8=89462/59049, c_10=43564781/28697814. These follow from the finite exact ideal tree, not a fit to computed cone counts. For g=17 the coefficient is approximately 1.51902007.

## 2. Main spine and all off-spine departures

Use the exact unified grammar and the valuation/drop bound a<=2*delta from [FixedLevelWindow.md](FixedLevelWindow.md). Put K=N-1, T_k=8*2^k+k, D=4N+6. The only even predecessor of the fatal target is u_0=T_K-D. Its complete same-level inverse ray is

    u_j=T_K-D*2^j,  0<=j<=J,
    J=floor(log2((T_K-F(K)-1)/D)) = N-log2 N+O(1).

A same-level inverse parent is unique and even. No same-level parent of F(N) is possible, by strict growth and its minimal height at level N. Any other immediate parent of the fatal target must be odd and at a lower level.

**No even cross-level departure from the canonical spine is possible for all sufficiently large N.** An even inverse edge to level K-1 would require u_j<=4*2^K-3, as well as u_j>F(K). Hence

    4*2^K+K+3 <= D*2^j <= 4*2^K+2K+3.

The positive difference D*2^j-4*2^K is then at most 2K+3 and divisible by 2^j (since j<=J<K+2). Yet the first inequality implies 2^j>=4*2^K/D>2K+3 for large N. Contradiction. Even parents at still lower levels are excluded by the at-most-one even level jump. Thus every genuine departure from the canonical spine is odd.

The subtrees of the other, odd immediate parents of F(N) have O_g(1) nodes. Indeed in the normalization x=(h+k+4)/2^k the fatal target starts exactly at x=4. Follow the parallel ideal path starting z=4. After the first odd edge its numerator modulo 3 is nonzero with denominator 3^A, 1<=A<=2g; this stays true under all further edges. The small positive error estimate from the one-free-ray lemma applies to the first alleged same-level run of S=bit_length(4*3^(2g)) edges. It forces all post-odd ideal values strictly between 4 and 8 and deficit at least 1/3^(2g), so S consecutive same-level edges are impossible. There are only O_g(1) jump labels and bounded run lengths. This argument does not require the first ideal value to start at 8.

## 3. The nonresonance argument for late canonical positions

A naive concern is that at a late canonical position, an odd crossing could land arbitrarily close to the upper seam at a lower level and produce a second order-N even ray. In fact the exact integrality of the first odd departure rules out every such seam resonance.

Use a different normalization here:

    y=(h-k)/2^k.

Its source band is between 4-(2k+4)/2^k and 8-(2k+5)/2^k. A reverse edge from level L to k, delta=L-k, satisfies

    y_parent = C*y_child - 8 + eta,
    eta=((2/3)^a*(2L+5)-(2k+5))/2^k.

In particular same-level even edges have eta=0. For a fixed canonical position j, start an ideal path at the **exact** normalized coordinate

    z_0 = y(u_j) = 8-D*2^(j-K),

and subsequently use z'=C*z-8 with no eta term. The genuine first departure is odd, a>=1, so the exact grammar forces 3|(2u_j+5). Since N mod3 is 1 or 2, 2K+5=2N+3 is a unit modulo3. Thus the initial scaled ideal numerator P_0=u_j-K is a unit modulo3.

At a later ideal node of level k, define A as cumulative valuation and P=3^A*2^k*z. It is an integer, since

    P' = 2^(a+1)*P - 8*2^k*3^(A+a).

After the first odd edge A>=1, and reduction modulo3 shows P remains a unit forever. Consequently **no post-odd ideal value is dyadic**: an equality z=m/2^b would imply P*2^b=m*3^A*2^k, impossible modulo3. This includes both seams 4 and 8. The locally kernel-checked modular proof is in SeamNonresonance.lean. This rules out exact resonance even when the starting late coordinate depends on N.

Let R be the constant from the one-free-ray lemma in FixedLevelWindow.md. For each late position J-R<j<=J, q=max(0,K-j)=O_g(log N). The ideal starting coordinate has denominator dividing 2^q. Every later ideal value has denominator dividing 2^q*3^A, because the affine maps multiply by an integral power of2 and divide only by 3^a. Therefore after the first odd edge,

    |8-z| >= rho, |4-z| >= rho,  rho=1/(2^q*3^(2g)).

Set H=q+ceil(log2(3^(2g)))+3. Consider any genuine prefix up to and including the first alleged same-level run of H edges (or any earlier prefix). It contains at most g jumps and at most (g+1)H same-level edges. Total valuation <=2g and total level drop <=g. A product of its affine coefficients, or any subproduct, is at most 2^(3g+g+(g+1)H). Each correction has magnitude <=(4N+10)/2^(N-g). Since q and H are O_g(log N), the absolute accumulated ideal error is bounded by a polynomial in N times 2^(-N), hence less than rho/4 for every sufficiently large N, uniformly over all prefixes. The actual band correction from [4,8] is also less than rho/4. The dyadic separation therefore forces every post-odd ideal prefix into the strict interval (4,8).

Each same-level ideal reverse edge doubles the deficit 8-z. Starting from deficit >=rho, H edges make the deficit >=8, contradicting the strict ideal band. The first-violation argument proves that **every** same-level run after any late departure has length <H=O_g(log N). No exceptional-index assumption or heuristic equidistribution is used.

It follows that the total late-departure subcone has O_g(log N) nodes, rather than O_g((log N)^g). There are at most R late spine positions and O_g(1) possible immediate odd parents at each. For each such parent, repeat the path-counting proof of FixedLevelWindow.md with its maximum ray length N+3 replaced by H+1. Partition the paths by their first early crossing exit (or terminal run): earlier exits have at most R choices, the distinguished run at most H+1, and all later runs fewer than S choices by the one-free-ray lemma. The jump-label sequences are still bounded by 6^g. This is a uniform O_g(H) bound. The same-level bound here applies to rays *starting at any genuine node of the late subcone*, since appending such a run to the already genuine path would give a first violating prefix.

## 4. Early departures and exact coefficient

For each early canonical position j+R<=J, apply the original one-free-ray argument to the ideal path starting at upper seam z=8 in the x-normalization. Its first crossing is odd, every ideal value after that is strictly between 4 and 8, and every later same-level run is bounded by S. Thus every such genuine path gives one of the finite words in the formula for c_g.

Conversely Section 5 of FixedLevelWindow.md proves, for every fixed such word w and every sufficiently large surviving N, exactly

    N/(2*3^(A(w)-1))+O_w(log N)

realizations at canonical indices j. The congruence is exact: its coefficient and constant numerator are units mod3, and 2 generates the units modulo 3^A. The terminal integrality implies integrality of all previous heights. A fixed sufficient early margin assures every intermediate source band, and only O_w(log N) boundary indices can affect the count. Removing the last R spine positions changes this count by at most R. The finite word set depends only on g, so summing the errors gives O_g(log N).

Every inverse path to a given ancestor is unique because the forward reset is deterministic and strictly increases height. Thus the early words and j values, canonical spine, late subtrees and other initial odd subtrees are disjoint. The canonical spine has J+1=N+O(log N) vertices. The initial target and other immediate odd subtrees contribute O_g(1), and all late off-spine branches contribute O_g(log N). This proves the all-index asymptotic and its per-level version.

## 5. Reproduction

Use the existing exact compressed enumerator and ideal_seam_tree. With deterministic RNG seed746, at each gap 2,4,6,8,10 choose five pseudorandom base indices in [2000,10000) and five in [20000,100000), shift each to residue4 mod6, and include its residue5 successor. Across these 100 cases, the maximal absolute discrepancy |A_g(N)-c_g*N| divided by bit_length(N) was respectively 1.389, 1.758, 2.828, 3.408, 4.446. This is illustrative finite evidence for the proved asymptotic, not a bound on its implicit constant. The complete exact compressed algorithm was independently checked against explicit reverse sets in the preceding fixed-window work.

## Scope

This establishes the exact leading coefficient uniformly across every surviving fatal index at any fixed gap. It removes the possible resonance-based source of additional linear branches, rather than merely counting a sparse generic subset. It does **not** give uniform control as g grows to N, nor exclude reachability from blank-root height 2. The all-time decision for #746 and BB(6) remains open.
