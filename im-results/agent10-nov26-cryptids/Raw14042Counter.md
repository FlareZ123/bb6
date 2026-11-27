# Sibling 42: two-way bank and finite root connection
Machine codes [7,21,11,12,15,1,6,18,4,17,3,24], i.e. 1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_1RA---. Blocks nearest first, three bits little-endian. See Raw140OrbitCore.lean.
## Accepted left-bank law
Raw14042Bank.return42, CI 46005422665 at 3d7898d3117d3bb956ca7c593e29b2ad1a87458f, proves reachability for all p>=1 and n>=2:
```
AR(3^p2,(115)^n s) -> AR(3^(p+12)2,(115)^(n-2+epsilon(s))rho(s)).
```
s runs through 542,152,1121,5215,1155,11511 cyclically, with epsilon=1 on the last only. The local common-table law finish42Any has cost 54p+403 and holds for ER(33325 3^p2,1Y) with arbitrary Y. pumpAny converts ER(333(133)^j X,1Y) to ER(333X,1(115)^jY), cost 21j. Hence the earlier n>=3 restriction is unnecessary.
## Opposite counter
For the six suffixes tau=31,32,315,325,3242,35221 in cyclic order, let e=1 for the last and zero otherwise. New symbolic local rules (generator generate_raw140_42_counter.js; CI 46006145491 accepted) imply:
```
ER(27 3X,3 2^m (322)^j tau) ->
ER(27X,3 2^(m+1) (322)^(j+e) rho(tau)).
```
Proof: ER(2Z,32Y)->ER(26Z,3Y), cost 19. Iterate m times, then ER(2Z,3322Y)->ER(2662Z,3Y), cost 45, j times. This gives ER(2(662)^j6^m7 3X,3tau). Apply the six finite suffix paths prep31,...,prep35221 to reach BL((662)^j6^m7 3X,22 (322)^e rho(tau)). Their costs are 54,76,54,78,92,64. BackTrip BL(662X,223Y)->BL(X,223223Y) costs 21; iterate j times, then BL6^m costs 3m. Finally BL(73X,22Y)->ER(27X,32Y) costs 21. Total 22m+66j+c_tau+21. The context X is untouched. This is an inductive identity, not fitted growth data; full induction is not yet in Lean.
At exhaustion k=0 with X=2, the alternate last move BL(72,22Y)->ER(26,32Y) costs 21. Repeat the forward/suffix/back sweeps once and sweep the final sixes to reach BL([],2^(m+4)(322)^(j+1)32) when tau=35221 at exhaustion (the second prep is 31->32).
## Root connection
Independent unaccelerated primitive simulation (Set of nonblank cells, integer head) at t=554115 gives q=A, head=125, L=3^276 2, R=(115)^21 152. RLE execute uses 81724 iterations after primitive step 2; formal finite certificate not yet built. Eleven accepted left-bank returns reach AR(3^408 2,115542). The symbolic local low542 identity (accepted) maps AR(3^p2,115542) to AR(3^(p+12)2,[]) for p>=1. SeedCounter gives AR(3^7 X,[])->ER(27X,3 2^7 31), cost 635. With 413 counter iterations, the root reaches ER(272,3 2^420 (322)^68 35221). The depletion steps above yield BL([],2^424(322)^69 32).
The initTwos and twoPump paths give BL([],22Y)->AR(332,2Y), then AR(3^p2,222Y)->AR(3^(p+4)2,2Y). Apply 211 iterations to get AR(3^846 2,2(322)^69 32). BoundaryOne maps AR(3^p2,23Y)->AR(4 6^(p+2)4,Y). Thus the next target is AR(4 6^8484,22(322)^68 32). Later raw RLE simulation from that target reaches AR(3^1303 2,2) after 2290539 further primitive steps (not yet a symbolic recurrence). Investigate that configuration instead of repeating root simulation.
## Accepted right-bank law
Raw14042Right.rightReturn42 (CI 46007150191 at 04c56d8d639c064aff437cdb1fb54a4105192703) proves, for all p>=0 and n>=2:
```
BR(5^p,(644)^n s) -> BR(5^(p+12),(644)^(n-2+carry(s))rho(s)).
```
Here s cycles through 62,64,6221,6421,6405,62542; carry is 1 only on the last. Proof: variant-specific 80-step initial conversion consumes two triplets and enters CR(4 55525 5^p,6Y). Common-table scan consumes another triplet for 45 steps and prepends 554 behind the 4 marker; tail turn changes the finite suffix and optionally adds one triplet; DL pump removes each 554 behind the 5 marker, producing 644 in 21 steps. The remaining defect 5555 2 5^(p+1) is absorbed into 5^(p+12) by an exact affine-time common-table path. See generate_raw140_42_right.js and Raw14042Right.lean.
## Next low-bank bridges (paper calculations, not yet composed in Lean)
AR(3^1303 2,2) reaches DL(6^1299 4,4^8 62) after 8444 steps; existing dIter/dEndE/eEven imply BR(5^2616,(644)^216 6421). The accepted right-bank return iterates 118 times to BR(5^4032,64). A local finite sweep reaches BR(5^4037,[]). Blank-B seed BR(5^p,[]) -> ER(1 333 5^(p-4),152) for p>=4, cost244; 4033 ER rotations produce a 672-triplet 133 bank with suffix1121. prep1121/prepareCarry/pumpAny and an odd-bank homogeneous exit (not yet verified) suggest AR(3^8080 2,(115)^671 5215), then 366 left-bank returns give AR(3^12472 2,5215).
For the latter a finite symbolic seed candidate is AR(3^p 2,5215) -> ER(27 3^(p-8) 2,3 2^3 4 6 4^2 6405) for p>=8, cost726. A mixed counter pair can be derived from the previously accepted CR/DL word bounce: ER(27 33X,3 2^m 4 6 W s) -> ER(27X,3 2^(m+1) 4 6 4 W (644)^carry(s) rho(s)), W an arbitrary word over 4,6, s in the right tail cycle. The two marker phases 4 and 5 each scan m twos; local prep for a leading 4 of payload changes it to 6, while leading 6 triggers the arbitrary-word bounce and one suffix rotation. Compose the two marker phases; detailed endpoint checks still needed. This may allow a finite symbolic grammar for depleted-bank cases instead of numerical exploration of very large p.
No closed infinite orbit, no nonhalting Cover for sibling42, and no global roster reduction yet.
