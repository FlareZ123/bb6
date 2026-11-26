# F421: exact principal macro and regular-cell binary countdown

**Status:** paper derivation and reproducible finite computation. The original-machine Lean bridge and an all-time invariant remain open. This is a refinement of [the frontier transduction](FrontierTransduction.md), not a resolution of F421.

Write P=10, Q=01, Z=00, R=11, with the left word read near-to-far. The authentic principal frontier is P Q^3 at primitive time 24, head 4. The right side is 1 followed by blanks.

## Principal phase

For an input beginning P^a Q, a>=1, use the first-return parser and cost in FrontierTransduction.md. If the parse reaches the bad token 111, stop at the first F1 read. Otherwise, if L is the consumed length, the first output has form P^r Z W, where r=a+1 for even L and r=0 for odd L. For the even case, the first a continuing tokens produce (01)^a, so the leading 1 in X pairs with them to give P^a and a remaining 1. The next Q must either be the start of continuing token 010 (whose output 101 makes the next pair R, mapped to Z), or the terminal 011; the latter has odd L. The additional leading P is the even-return prefix. The odd-return prefix is Z directly.

The second return parses P^r followed by Z, a safe aligned d terminal, and gives P^(r+1) Q W. Its cost is 4r+6 and displacement 2. Thus a principal macro comprises two returns, with the second unconditionally safe, and preserves the principal phase whenever the first is safe. The leading exponent evolves a -> a+2 for an even first return, a -> 1 for an odd first return. In particular a stays odd on the authentic orbit.

## Regular carry cells

Consider P^a Q^b followed by m cells P^p_i Z^e_i Q^q_i (e_i in {0,1}) and an arbitrary suffix U. Require a>=1, b>=2, all p_i>=1 and q_i>=2. Define the little-endian marker integer V=sum e_i 2^(i-1). For V>0, let j be its first set bit.

The scan terminates safely at the Z of cell j. The identity behind this is the exact tokenization

    Q^q P^p = 010 (10)^(q-2) 110 (10)^(p-1)

for q>=2, p>=1, producing 101 (01)^(q-2) 011 (01)^(p-1). Starting with the remaining 1 from the preceding pair, this output gives R Q^q P^(p-1), with another remaining 1. The final d contributes 1, giving R. Consequently the first return gives P^(a+1) Z Q^b, followed by P^(p_i-1) Z Q^q_i for i<j, then P^(p_j-1) Q^(q_j+1) and the unchanged deeper suffix. Applying the safe second return yields

    a <- a+2, b <- b+1
    for i<j: p_i <- p_i-1, e_i <- 1
    at i=j: p_j <- p_j-1, e_j <- 0, q_j <- q_j+1

with all other entries fixed. The formula holds even if a run length becomes zero, but the regular-cell representation may then collapse. The marker integer decreases by exactly one. The first scan has half-length a+b+sum_{i<=j}p_i+sum_{i<j}q_i+1 and exactly b+sum_{i<j}q_i bounce pairs. The combined primitive cost is

    8(a+b) + 4 sum_{i<=j} p_i + 8 sum_{i<j} q_i + 16,

and head displacement is +4.

## Closed-form skip

For 0<=k<=V, put W=V-k, d_i=2^(i-1), A_i=floor(V/d_i), B_i=floor(W/d_i). Define

    n_i = A_i-B_i
    t_i = floor((A_i+1)/2)-floor((B_i+1)/2)
    s_i = n_i-t_i
    epsilon_i = A_i mod 2.

If every n_i<=p_i-1, all k macros preserve the regular representation and are safe, independent of U. Indeed cell i is visited exactly when the descending marker integer is divisible by d_i; among those visits the terminal ones have odd quotient. Terminal and nonterminal visits alternate, the first being terminal iff epsilon_i=1. Induction on k therefore gives the endpoint

    a'=a+2k, b'=b+k, p_i'=p_i-n_i,
    q_i'=q_i+t_i, e_i'=floor(W/d_i) mod 2.

Summing the per-macro costs gives the exact primitive count

    8k(a+b)+12k(k-1)+16k
    +4 sum_i (n_i p_i - n_i(n_i-1)/2)
    +8 sum_i (s_i q_i + s_i(s_i-1)/2 + epsilon_i s_i).

The displacement is 4k. The safe maximum k, bounded by a requested limit, is min(V, limit, min_i(V mod d_i+(p_i-1)d_i)). The strict positive-run constraint intentionally excludes degeneracies. No assumption on the deeper suffix is used.

## Implementation and evidence

`compressed.cpp` implements the first parser as a finite-state run transducer with a delayed output pair, then applies the second-return prefix rewrite. Repeated same-symbol transitions reach fixed states; work is proportional to the number of pair runs. `carry.cpp` implements the closed-form skip above with a multiprecision marker integer and 128-bit primitive count, falling back to the compressed single macro at exceptional boundaries.

Build and reproduce from this directory:

    g++ -std=c++20 -O3 compressed.cpp -o compressed
    g++ -std=c++20 -O3 carry.cpp -o carry
    python3 test_compressed.py
    ./carry 100000 --check
    ./compressed 20000000
    ./carry 20000000
    ./carry 1000000000000000000

Local testing matched 12,000 word-formula comparisons and all expanded skips through 100,000 macros. Independent per-macro and carry runs matched the complete endpoint and exact count at 20,000,000 macros (658805567505964 primitive transitions). The 10^18 run returned:

    macros=1000000000000000000
    steps=2741467853641781568730607840197912170
    head=3999999999999999478
    odd=526 runs=191 maxruns=242
    skips=955 skipped=999999999999999014 singles=986
    largest=72057594037927935

The 10^18 run is a finite safe prefix of the partial machine, not a halting lower bound on BB(6). Its arithmetic is within the implementation's documented input bound; source-level verification remains necessary.

## Unresolved edge

The skip ends when the regular marker integer is zero or a positive P run would disappear. The first-return parser may then enter the exceptional tail. The main research target is a closed odd-epoch/tail invariant that handles these boundaries and either excludes 111 forever or determines its first occurrence. A finite safe prefix, regardless of length, cannot discharge this obligation.
