# Uniform growing-window asymptotic for #746

**Status:** mathematical proof using the exact source-certified ResetParent grammar, the previously established fixed-window geometric argument, and the locally kernel-checked ideal-word entropy estimate in SeamMass.lean, SeamPrefix.lean and SeamEntropy.lean. The asymptotic estimate below is a paper proof, not a formal source-connected Lean theorem. It does not decide blank-root reachability.

## Theorem

Let F(N)=4·2^N−N−4. Let A_g(N) count its distinct ResetParent ancestors (including F(N)) in levels N−g through N, for surviving gate indices N mod 6 in {4,5}. Let c_infty be the convergent ideal-seam mass defined in [SeamMass.md](SeamMass.md).

For each fixed 0<epsilon<1/2, along **all** surviving gate indices N and all integer window functions satisfying

    g(N) → infinity,
    1 ≤ g(N) ≤ (1/2−epsilon) log N / log log N,

we have

    A_g(N)/N → c_infty,     1.51902529 < c_infty < 1.551323.

Here log denotes the natural logarithm. In particular the limit holds on an unbounded number of lower levels simultaneously. No interchange of a nonuniform fixed-gap O_g estimate with a growing limit is needed: the following explicit error controls the joint limit.

## 1. Explicit constants

Use the notation of [FixedLevelWindow.md](FixedLevelWindow.md):

    B=3^(2g), S=bit_length(4B), T=g(S+1),
    M=4g+gS+bit_length(B)+bit_length(T)+1,
    R=M+3, L=2M+2g+12.

Set K=N−1, D=4N+6, and

    J=floor(log2((4·2^K+2K+3)/D)).
    Q=R+ceil(log2 D)+3,
    H=Q+bit_length(B)+3.

For the estimates below assume N is sufficiently large and N−g≥L, J≥R, and

    g·2^(4g+gH)·(4N+10)·2^(−N+g) < 1/(4·2^Q·B),
    (2N+5)·2^(−N+g) < 1/(4·2^Q·B).                  (1)

All these requirements hold uniformly for 1≤g≤log N when N tends to infinity: M,R=O(g²), Q,H=O(g²+log N), so the powers in (1), apart from −N, are O((log N)^3). They are also directly checkable at any proposed (N,g).

We show the quantitative estimate

    |A_g(N)−c_g N|
      ≤ 1+|J+1−N|+(N−(J−R+1))(c_g−1)
        + (27/14)·3^(2g)
        + R(g+1)(H+1)(6R)^g + (6S)^g.              (2)

Here c_g is the finite ideal mass with total level drop at most g−1, as defined in FixedLevelAsymptotic.md. The constants are deliberately conservative.

## 2. Early canonical exits: simultaneous exact realization

The unique even inverse ray from F(N) has heights u_j=8·2^K+K−D·2^j, 0≤j≤J. No even cross-level departure is possible when N is sufficiently large: the divisibility argument in FixedLevelAsymptotic.md §2 requires only N large, independently of g.

Let I=J−R+1 count the early positions j+R≤J. For every ideal word w from seam 8, with first edge odd and total drop ≤g−1, write A=A(w)≥1 for its total valuation. The valuation bound gives A≤2g. Every strict-band ideal value after the first edge has denominator dividing 3^A and numerator a unit modulo 3, hence distance at least 1/B from either seam. Each ideal same-level run has fewer than S edges by doubling its initial deficit. Thus every ideal word has at most g jumps and gS same-level edges.

At an early position, use x=(h+k+4)/2^k. The initial error 8−x is nonnegative and at most 5·2^(−R)<2^(−M). Continue the affine maps over rational heights, without first demanding integrality. Their real corrections satisfy 0<epsilon_i≤(2N+4)2^(−N+g)≤2^(−M), as in the one-free-ray lemma. The product of all multipliers, or any subproduct, is at most 2^(4g+gS), because each ideal multiplier exceeds 1, and the exponent budget counts all jumps, valuations and same-level edges. The accumulated error is at most (T+1)2^(4g+gS−M)<1/(2B). Consequently every intermediate rational height lies strictly above its lower band seam; the upper margin is at least 1/B, exceeding 2^(−k). These are genuine strict source bands whenever the heights are integers.

The terminal height has expression (P+Q'·2^j)/3^A. Both P and Q' are units mod 3: the first odd edge introduces the denominator 3^a, its constant coefficient reduces to a power of 2 times 2T_K+5, and its coefficient of 2^j reduces to a power of 2 times −D. Both factors are units on the surviving sectors. Every subsequent step multiplies these numerators by a power of 2 modulo 3. Terminal integrality selects a unique j mod 2·3^(A−1), since 2 generates the units modulo 3^A. Integrality of the terminal height implies integrality of all earlier heights (multiplication by a power of 2, division by a power of 3 and integer addition cannot cancel a nontrivial ternary denominator). Thus the exact number of real paths realizing w from the I early positions differs from I/(2·3^(A−1)) by at most 1.

Conversely, the one-free-ray lemma forces every genuine early departure in the window to a strict-band ideal word, by the same positive error bound. All words and positions correspond to distinct ancestors by strict forward growth and determinism. Hence the total early contribution differs from I(c_g−1) by at most the number of ideal words. The formal entropy theorem gives N_A≤(9/7)(16/9)^floor(log2(3^A))≤(9/7)3^A. Summing for 1≤A≤2g bounds this error by (27/14)3^(2g).

## 3. Late canonical exits: uniform nonresonance and one free ray

There are at most R late canonical positions. At any such j, q=max(0,K−j)≤Q, since J≥K+2−ceil(log2 D). In y=(h−k)/2^k coordinates the exact starting y_0 is dyadic with denominator dividing 2^q. Compare the genuine inverse path with its ideal path started at this exact y_0.

Every departure is odd. The first odd edge forces 3|(2u_j+5). Since 2K+5=2N+3 is a unit mod 3, the initial scaled numerator P_0=u_j−K is also a unit mod 3. At level k after cumulative valuation A, the scaled ideal numerator P=3^A·2^k·z is an integer, and each edge changes it by

    P'=2^(a+1)P−8·2^k'·3^(A+a),

where k' is the new level. It stays a unit modulo 3. After the first odd edge the ideal coordinates cannot be dyadic, in particular cannot equal 4 or 8. Since their denominators divide 2^q·3^A, they are separated from both seams by at least rho=1/(2^Q·B).

Consider a real prefix through the first alleged run of H same-level edges, or any shorter prefix. There are at most g jumps and gH same-level edges, since there are no same-level edges before the first odd departure. In y coordinates the per-edge correction is zero on same-level edges, otherwise at most (4N+10)2^(−N+g) in absolute value. Every real multiplier exceeds 1 by the x-coordinate identity. Their product and every subproduct are bounded by 2^(4g+gH). The first inequality in (1) bounds the accumulated ideal error by rho/4. The real y band differs from the ideal band by less than rho/4 by the second inequality in (1). Separation by rho therefore forces each post-odd ideal value strictly into (4,8). Each same-level ideal edge doubles the deficit from 8. H such edges would make an initial deficit at least rho exceed 4. This contradiction proves the uniform H bound for every post-departure run.

Now fix one late position. There are at most 6^g sequences of jump labels (positive level drops and their possible valuations). For any sequence with m≤g jumps, partition by the first early crossing exit, or the terminal run if there is no early crossing. Before that exit there are at most R late choices per run, the distinguished run has at most H+1 choices by the uniform bound (the initial run at the fixed departure has only one choice), and all following runs have fewer than S≤R choices by the one-free-ray lemma. Thus at most (g+1)(H+1)R^g paths per label sequence. Multiplying by 6^g and by R late positions gives the penultimate term of (2). This uses no distribution assumption about N or j.

## 4. Direct odd departures from the gate

Apart from its canonical even parent, every immediate parent of F(N) is odd. In x coordinates start its comparison ideal path at 4. After the first odd edge its ideal numerator is again a unit mod 3 and the positive error bound of the one-free-ray argument (now with zero initial error) forces a strict-band ideal value. The same first-violation argument bounds each post-odd run by S−1. For each of at most 6^g jump-label sequences there are at most S^g choices of all even runs, so this contribution is at most (6S)^g.

The gate itself, the J+1 canonical spine nodes, early and late canonical departures, and direct odd departures partition all ancestors in the window. Combining their contributions proves (2).

## 5. Uniform limit

The explicit constants satisfy R=O(g²), H=O(g²+log N), and J+1=N−O(log N). The convergent ideal-mass bound supplies a uniform bound on c_g. Under the displayed growth condition,

    log((6R)^g) = 2g log g+O(g)
                ≤ (1−2epsilon+o(1)) log N.

The remaining polynomial factors R(g+1)(H+1) are N^o(1). Thus the late contribution is o(N), uniformly, and (6S)^g and 3^(2g) are also o(N). All other terms in (2) are O(g²+log N). It follows that A_g(N)/N−c_g→0. Since g→infinity and SeamMass.md proves c_g→c_infty exponentially, the theorem follows.

For any fixed epsilon and g tending to infinity, this also gives A_g(N)=O(N) on these growing windows, and each omitted ideal-mass tail decays geometrically in g. The remaining barrier is still the gap from these upper levels down to the authentic root at height 2. The bound is on number of ancestors, not on the existence of a particular root path. It neither excludes all gate indices nor establishes machine nonhalting.
