# Sibling 42: two-way bank and finite root connection
Machine codes [7,21,11,12,15,1,6,18,4,17,3,24], i.e. 1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_1RA---. Blocks nearest first, three bits little-endian. See Raw140OrbitCore.lean.
## Accepted left-bank law
Raw14042Bank.return42, CI 46005422665 at 3d7898d3117d3bb956ca7c593e29b2ad1a87458f, proves reachability for all p>=1 and n>=2:
```
AR(3^p2,(115)^n s) -> AR(3^(p+12)2,(115)^(n-2+epsilon(s))rho(s)).
```
s runs through 542,152,1121,5215,1155,11511 cyclically, with epsilon=1 on the last only. The local common-table law finish42Any has cost 54p+403 and holds for ER(33325 3^p2,1Y) with arbitrary Y. pumpAny converts ER(333(133)^j X,1Y) to ER(333X,1(115)^jY), cost 21j. Hence the earlier n>=3 restriction is unnecessary.
## Opposite counter
For the six suffixes tau=31,32,315,325,3242,35221 in cyclic order, let e=1 for the last and zero otherwise. New symbolic local rules (generator generate_raw140_42_counter.js; CI 46005867631 initially pending) imply:
```
ER(27 3X,3 2^m (322)^j tau) ->
ER(27X,3 2^(m+1) (322)^(j+e) rho(tau)).
```
Proof: ER(2Z,32Y)->ER(26Z,3Y), cost 19. Iterate m times, then ER(2Z,3322Y)->ER(2662Z,3Y), cost 45, j times. This gives ER(2(662)^j6^m7 3X,3tau). Apply the six finite suffix paths prep31,...,prep35221 to reach BL((662)^j6^m7 3X,22 (322)^e rho(tau)). Their costs are 54,76,54,78,92,64. BackTrip BL(662X,223Y)->BL(X,223223Y) costs 21; iterate j times, then BL6^m costs 3m. Finally BL(73X,22Y)->ER(27X,32Y) costs 21. Total 22m+66j+c_tau+21. The context X is untouched. This is an inductive identity, not fitted growth data; full induction is not yet in Lean.
At exhaustion k=0 with X=2, the alternate last move BL(72,22Y)->ER(26,32Y) costs 21. Repeat the forward/suffix/back sweeps once and sweep the final sixes to reach BL([],2^(m+4)(322)^(j+1)32) when tau=35221 at exhaustion (the second prep is 31->32).
## Root connection
Independent unaccelerated primitive simulation (Set of nonblank cells, integer head) at t=554115 gives q=A, head=125, L=3^2762, R=(115)^21 152. RLE execute uses 81724 iterations after primitive step 2; formal finite certificate not yet built. Eleven accepted left-bank returns reach AR(3^4082,115542). The symbolic local low542 identity (pending CI) maps AR(3^p2,115542) to AR(3^(p+12)2,[]) for p>=1. SeedCounter gives AR(3^7 X,[])->ER(27X,3 2^7 31), cost 635. With 413 counter iterations, the root reaches ER(272,3 2^420 (322)^68 35221). The depletion steps above yield BL([],2^424(322)^69 32).
The initTwos and twoPump paths give BL([],22Y)->AR(332,2Y), then AR(3^p2,222Y)->AR(3^(p+4)2,2Y). Apply 211 iterations to get AR(3^8462,2(322)^69 32). BoundaryOne maps AR(3^p2,23Y)->AR(4 6^(p+2)4,Y). Thus the next target is AR(4 6^8484,22(322)^68 32). Later raw RLE simulation from that target reaches AR(3^13032,2) after 2290539 further primitive steps (not yet a symbolic recurrence). Investigate that configuration instead of repeating root simulation.
No closed infinite orbit, no nonhalting Cover, and no global roster reduction yet.
