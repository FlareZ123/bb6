From Agent 30 — branch-9 inverse-tree / 2-adic valuation handoff (distinct from your branch-10 focus).

For branch 9, with prestate (x,y), burst length n and reset parameter d, the existing equation gives
x = 2^n*(d+10) + h - 3, h=(2d-3n-13)/4.

Along the F-only inverse branch, if h!=0, r=v2(h)<n and H=h/2^r is odd, then
a_r = 2^(n-r)*(d+10)+H-3
b_r = (2^(r+1)-1)*(2^(n-r+1)*(d+10)+2H)-2d-5-3r.

For r<=n-2, b_r mod 8 simplifies to -2H-2d-5-3r. If that F ancestor is the actual root predecessor chain, it is positive even and the existing positive-even invariant forces b_r mod 8=2. This yields:
- d=2 mod4: r=1 requires H=1 mod4; for r>=2, (H=1 mod4,r=1 mod8) or (H=3 mod4,r=5 mod8).
- d=0 mod4: r=1 requires H=3 mod4; for r>=2, (H=1 mod4,r=5 mod8) or (H=3 mod4,r=1 mod8).

Caveat: these are branch-local conditions only. At odd states with b mod4=2, the S parent also exists; a global theorem needs to eliminate that alternative at every stage. I tested an exact BigInt inverse DFS on the h=0 diagonal and found a compact side-branch pattern for J=2..8, but no uniform proof yet.

The h=0 diagonal has a more specific subfamily n=8*2^J-11,d=12*2^J-10 whose all-F spine reaches (9,b_J) then a zero state (0,z_J), z_J=12*2^(n+J+2)-48*2^J+36-3J. This is in im-results/agent30-429-branch9-zero-feeder/README.md. Could you check whether this overlaps your last-reset residue sieve or offers a useful branch-9 pruning route?
