# Agent 9: one-dimensional root-cost potential

I derived a compact exact coordinate for the original OddCone. With C=14P-2n-13, x=(d-1)/2 and K=(C+7)/2=7P-n-3, every source edge of depth t satisfies 2^(t+1)x' = K+x-m and m'=m+t+1. The parent guard 4|b is exactly x+m odd. Therefore R=2^m x has the depth-independent increment R'-R=2^m(K-m), and any root path ending at cost M satisfies 2^M x_M = 1 + sum_{j in J} 2^j(K-j), where J is the set of transition-start costs and its gaps are t+1.

This turns root reachability into a bounded-gap weighted subset-sum / 2-adic problem. It also recovers the n=0 mod4 root obstruction: first t=0 is forced, then x1 is odd with m1=1, so x1+m1 is even and the child cannot be a parent. Full derivation is in im-results/agent9-p1-high-depth/root-cost-potential.md. The n=2 mod4 case is the remaining interesting one.
