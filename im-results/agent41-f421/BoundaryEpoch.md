# F421: complete regular drains and secondary tail countdown

**Status:** exact paper-level extensions of [CarryCountdown.md](CarryCountdown.md) and executable arbitrary-precision experiments. No all-time root verdict or new Lean acceptance. The complete-drain lemma handles terminal cell collapse, and the secondary countdown reduces the authentic exceptional phase to a new arithmetic boundary.

## Complete regular drain

Use P=10, Q=01, Z=00, H=11 and a regular word P^a Q^b ∏ P^{p_i} Z^{e_i} Q^{q_i} U, with a≥1, b≥2, p_i≥1, q_i≥2, e_i∈{0,1}, indexed near-to-far. The regular single-macro identity also applies when a P run reaches zero. A **terminal deletion** has e_i=1 on that visit, sets e_i=0 and merges Q^{q_i+1} into the preceding Q run. Nonterminal deletion is outside this theorem.

Compute from farthest to nearest, letting H_i count terminal events strictly farther than i:

    H_m=0
    N_i=2H_i+e_i, n_i=min(p_i,N_i)
    require p_i>N_i or p_i mod 2=e_i
    t_i=floor((n_i+e_i)/2), s_i=n_i−t_i
    H_(i−1)=H_i+t_i

The drain is safe, ends at zero surviving markers, and executes K=∑t_i macros, displacement 4K. Its endpoint is a→a+2K, b→b+K, p_i→p_i−n_i, q_i→q_i+t_i, dropping zero P runs and merging adjacent Q runs. The suffix U is unchanged.

**Proof.** A higher terminal event occurs only when all retained lower bits are zero and sets those bits to one. Each retained cell therefore has alternating visits: its initial e_i determines whether it starts with a terminal visit, and each higher terminal event supplies one nonterminal visit followed by a terminal visit before the next higher event or exhaustion. Lower cell disappearances change the time between visits, not that sequence. Thus the cell has 2H_i+e_i potential visits and n_i actual visits before exhaustion or disappearance. The parity guard makes any disappearance terminal, preserving all other positive runs. Induct from the highest cell. In particular the original fixed-width floor(V/2^i) count is incorrect after higher cells have disappeared, which can shorten lower countdowns.

### Exact primitive cost

For a macro at original cell j after k macros, attribute q masses to their original indexes even after mergers and p_i=0 for deleted cells. The cost from CarryCountdown becomes 8(a+b+3k)+4∑_{i≤j}p_i(k)+8∑_{i<j}q_i(k)+16, with original b. Leading merged q masses are counted exactly once by the latter sum. Summing gives

    8K(a+b)+12K(K−1)+16K
    +4∑[n_i p_i−n_i(n_i−1)/2]
    +8∑[s_i q_i+s_i(s_i−1)/2+e_i s_i+(H_i−s_i)(q_i+t_i)].

The last term accounts for higher terminal events after a lower cell disappears. A surviving cell has H_i=s_i. Endpoint and cost thus require one reverse cell pass even with many deletions. The parity-guard failure is a rejected certificate, not a halt.

## Secondary countdown

Write R(a,b,C) for the regular prefix with zero markers. The exceptional tail at an observed even epoch has form

    T=P^x Z P^y ∏ Z^{f_i} Q^{z_i} P^{r_i} U
    S=∑ f_i 2^{i−1}>0.

Here x≥4,y≥3,z_i,r_i≥2. Let j be the first set bit, with r_i≥3 for i<j. The exact cycle is conditional on the following primary guards and each regular drain being safe as in the preceding lemma.

1. **Even d macro.** All regular p_i≥2. Set a→a+2,b→b+1,p_i→p_i−1,e_i→1. The tail becomes P^{x−1} Q P^y followed by unchanged secondary cells. Cost 8(a+b)+4(∑p_i+x)+8∑q_i+16. Drain A.
2. **Odd e macro.** Require surviving p_i≥3. Odd grouping maps leading P^a Q^b to P Q^{a+1}; crossings Q^q P^p contribute P^q Z Q^{p−1}, because their continuing output is 101(01)^{q−2}011(01)^{p−1}. Including P^{x−1}, marked cells become (b,p_1−1), (q_1,p_2−1), ..., (q_last,x−2). Terminal Q P^y contributes a final unmarked (1,y−1,0). The remaining half-pair shift maps each Z^{f_i}Q^{z_i}P^{r_i} to Z^{1+f_i}P^{z_i−1}H Q^{r_i−1}, with pending zero before U. Length L=2(a+b+∑(p_i+q_i)+x)+1, bounce count B=a+∑(p_i−1)+x−2; odd principal macro cost 2L+7+4B. Drain B. Final unmarked cell untouched; the last marked cell has exactly one terminal visit and now q=x−1.
3. **Odd d macro.** Require p≥3 in the regular cells before final unmarked cell. Crossing Q^q Z P^s H Q^t uses continuing tokens 010(10)^{q−1}, 010(10)^{s−1}, 110(10)^t, the last consuming the first zero of the next Z. At the first Z² the remaining three zeros give the d turn and leave one zero for the shifted suffix. Pair the emitted words and apply terminal replacement. Each lower twisted cell contributes Z Q^{z_i} P^{r_i−1}; the terminal contributes Q^{z_j+1} P^{r_j}, reversing the half shift on the untouched higher suffix. The regular prefix is marked by the crossing rule except final p=1 gives P^{x−1} Z with no following Q from that cell. Thus new exceptional tail is P^{x−1} Z P^{y−1} ∏ Z^{f'_i} Q^{z'_i} P^{r'_i} U, with

       i<j: f'=1, r'=r−1, z'=z
       i=j: f'=0, r'=r, z'=z+1
       i>j: unchanged.

   If regular prefix includes final unmarked cell, L=2(a+b+∑(p_i+q_i)+∑_{i<j}(z_i+r_i))+3, B=a+∑(p_i−1)+∑_{i<j}z_i. Cost 2L+7+4B. Drain C.

This is secondary decrement S→S−1. After k cycles with all premises maintained, A_i=floor(S/2^{i−1}), B_i=floor((S−k)/2^{i−1}), n_i=A_i−B_i,t_i=floor((A_i+1)/2)−floor((B_i+1)/2),s_i=n_i−t_i give x'=x−k,y'=y−k,z_i'=z_i+t_i,r_i'=r_i−s_i,f_i'=B_i mod 2. The primary-prefix endpoint can be computed independently of the secondary tail, as shown below. The remaining general obligation is all-time guard closure and subsequent higher-level boundaries.

## Authentic root and evidence

At the zero-primary-marker frontier immediately before the even d macro after odd macro 190, x=1703916,y=262124 and 15 secondary (z,r,f) cells give S=32750:

    (32776,851959,0) (16387,557051,1) (860160,737276,1)
    (659454,778236,1) (2048,241660,0) (62463,219134,1)
    (63998,89087,1) (48382,101116,1) (1662,12415,1)
    (1854,27260,1) (926,8508,1) (847,8620,1)
    (1958,3527,1) (1106,2529,1) (41,2621,1)
    U=Q P^159 Z P^355 H Z P^112 H Z Q

Primary a=2047,b=3071 and zero-marker pairs (p,q):

    (2048,1535) (512,767) (3584,3967) (2816,4031) (384,3038)
    (960,3054) (224,3148774) (2621288,3145735)
    (7077811,2883586) (2883545,131073)

The local arbitrary-precision implementation reproduced the earlier 10^18-macro count. At 10^50 principal macros it reached 28573549291907737747121673600169498036340127855568021245374953124058438783837935224986696975611208306 primitive steps without F1 (1358 odd macros). The new full-drain run reached the 5000th odd macro, cumulative cost bit length 1245 and SHA256 of minimal unsigned big-endian cost bytes 156c30af941a0a3b0850c3d4c76a35c8edbba8f46a8f22547b582f722f039f88. 7503 complete drains, 7512 single macros, one strict skip near nonterminal deletion at odd 153. All 10000 randomized drain comparisons matched the strict-skip-plus-single engine. 422 secondary cycles through odd 1000 matched the exact single-macro engine at each of their three exceptional boundaries.

The consolidated reproduction script boundary.py implements the same equations. Commands:

    python3 boundary.py --test
    python3 boundary.py 1000 --cycle --check
    python3 boundary.py 100000000000000000000000000000000000000000000000000 --macros
    python3 boundary.py 5000

The --cycle option may include drain C after the final odd macro; compare identical frontier phases. These are finite experiments, not an all-time proof, source-accepted Lean result, or new BB(6) lower bound.

## Autonomous primary-prefix recurrence and the complete secondary-zero crossing

The next reduction removes all secondary-tail parameters from the primary-prefix endpoint calculation. In the three-drain cycle above, drain A is independent of x,y,z,r,f. At odd e, the last *marked* B cell has q=x−2 and p equal to the last q of A (or leading b of A when there are no cells). Its p is at least 2; it receives exactly one terminal visit because it is the highest marked cell, so it survives. The final unmarked (1,y−1,0) has no visits. The B-drain visit counts depend only on p and markers, not q. In the subsequent odd d crossing the surviving last marked B cell's q=x−1 becomes the tail P^{x−1}; it does not enter the C prefix. Consequently replace x−2 by any q≥2 (the implementation uses 2), omit the untouched unmarked cell, and compute the entire primary prefix autonomously. Guard p≥3 after B is still explicitly checked. This argument also applies when other marked cells disappear; the surviving last marked cell does not merge.

This gives the following exact finite check for the authentic odd-190 secondary epoch. The tail guard survives all 32750 decrements by the closed formulas (x=1671166,y=229374 at zero, all secondary z,r≥2); the primary guard is checked by the independent C++ integer recurrence for each cycle. The result is the zero-marker frontier immediately after 65690 odd principal macros and the following drain C. Its primary prefix has 8217 cells, leading a has 8218 bits, and the number of principal macros **since the odd-190 seed** has 8222 bits. Full decimal checkpoint SHA256 is f5e445d70cf1b2fc1982201911c6557b6c2b9fd5a1b9ee082e21be31758f2f87. Last ten (p,q) cells:

    38404096 2415918588
    86310912 939523837
    9601024 830472054
    11091968 180355001
    303104 16777183
    4345856 29360109
    1124352 33402812
    2359288 3145735
    6946811 2883586
    2818045 131073

The zero-tail is

    P1671166 Z P229374 Q49151 P835584 Q24575 P548864
    Q864254 P733183 Q661501 P776190 Q3071 P240637
    Q62975 P218623 Q64254 P88832 Q48510 P100989
    Q1726 P12352 Q1886 P27229 Q942 P8493 Q855 P8613
    Q1962 P3524 Q1108 P2528 Q42 P2621 Q1 P159 Z P355 H Z P112 H Z Q

The next even d and odd e are followed by an even e at the shifted Q1 boundary, instead of the secondary cycle's odd d. Exact general macros and drains traverse this transition; nonterminal deletion occurs in the following odd regime. At odd 65698 the primary prefix falls to two cells and a new very large tail run appears. Through odd 65710 (71 exact macro/drain actions after the secondary-zero frontier), no F1 is reached. The macro count since the odd-190 seed then has 8223 bits. This is a finite arithmetic crossing of the entire secondary countdown and its zero boundary; no all-time guard closure or universal nonhalting result.

Reproduce (the decimal checkpoint is about 20 MB; generate locally rather than commit it):

    g++ -std=c++17 -O3 prefix.cpp -o prefix
    ./prefix 32750
    sha256sum prefix-state.txt
    python3 cross_zero.py 20

For bounded execution environments, resume the prefix recurrence with a greater target, e.g. `./prefix 1000`, `./prefix 2000 prefix-state.txt`, etc. A complete run must end at target 32750; do not infer completion from a partial checkpoint. The crossing script's K excludes the initial path to odd 190 and is a principal-macro count, not a primitive-step total. The computation is not a new BB(6) lower bound. The next structural problem is the nonterminal deletion and higher-level exceptional tail.

