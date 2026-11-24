# Small signed delayed carry: exact full-P scan without large-integer transitions

Let P=2^n, C_j=n+j+3, Q=7P-n-3, and b_j in {0,1}. The full carry c_{j+1}=(c_j+(Q-j)b_j)/2 is legal iff integral. Start c_0=1. Represent c_j=7 W_j+s_j with W_0=0, s_0=1, 0<=W_j<P and W_j the last n bits, oldest bit at bit zero. The exact updates are

    W_{j+1}=floor(W_j/2)+(P/2)b_j
    s_{j+1}=(s_j+7(W_j mod 2)-C_j b_j)/2.

The signed update is integral iff the full update is integral. The signed state always lies in [-(n+j+1),7]. The window only needs to be reconstructed at block boundaries (and rare near-margin events). Within a block of n steps the delayed bits are fixed, so use u_0=s_0 at the block's root, u'=floor((u+7d)/2). The invariant u-C_j<s<=u gives unique reverse reconstruction of b: b=1 iff 2s'-7d<=u-C_j, and s=2s'-7d+C_j b. This is a proof of exact enumeration, including every legal branch. The nonnegative offset p=u-s has recurrence 2p'=p+C_j b-(u+7d mod 2), allowing a small bitset in future certificate work.

For requiredMargin L, if W and P-1-W are at least M, and 7M>=L+n+j+1, both full margins are >=L. A high selected and high omitted bit therefore suffice; track just last indices of each bit. When one is absent, its low window or complementary window fits in a machine integer and can be recovered exactly. The scanner chooses L=requiredMargin(n,cap), stronger than the required value if extinction K<=cap. At j=0, c=1 and the upper margin follows from n>safeExp. No full large integer is computed per state.

DelayCore.lean proves these algebraic facts (standard axioms only, Lean 4.36.0-rc2). delay.cpp implements a depth-first block enumeration with signed 64-bit arithmetic; n and cap must be positive within signed int bounds and their sum fit signed int. This is an exact computational algorithm, NOT yet a kernel-checked MarginSafe certificate. The previous breadth-first implementation was tested on all five large known exceptions and matches their exact depths.

Compile: g++ -O3 -std=c++17 delay.cpp -o delay
Run: ./delay N CAP (use cap=10*n for tested cases)
Modular screen extension: g++ -O3 modular_scan.cpp -o modular_scan; ./modular_scan 10002 1000000

New completed computation: n=164446, K=174338, cap=1644460, L=10195678, margin=true, visits=2238590254, near=0. Larger scans in progress. Existing known depths are reproduced for 286,350,1614,2990,3342. These results are not a universal P1 proof.
