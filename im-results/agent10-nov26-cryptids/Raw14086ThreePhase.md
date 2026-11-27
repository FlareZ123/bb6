# Raw140 sibling 86: three-phase expanding return system

Status: complete paper-level nonhalting argument, exact finite root and symbolic local-rule replay checked, arithmetic invariant checked by Lean 4.36.0-rc2. The original-machine Lean composition and parent integration remain unaccepted. No canonical roster reduction is claimed.

Table: 1RB1RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_1RC---, codes [7,23,11,12,15,1,6,18,4,17,11,24]. F1 is absent. Use the nearest-first three-bit block convention of Raw140OrbitCore. Exact primitive blank simulation for 6892 steps gives state A, head 38, configuration AR(3^39 2,2), with all exterior cells zero.

## Closed section and return map

Write A0(p)=AR(3^p2,empty), A2(p)=AR(3^p2,2), B0(p)=BR(5^p,empty). The domain is p>=24. Three rank-ordered suffix lists:
- B: 62,64,6221,6421,6405,62542, triplet 644.
- C: 31,32,315,325,3242,35221, triplet 322, prefix 2.
- A: 542,152,1121,5215,1155,11511, triplet 115.
Let next(s)=(s+1)%6 and carry(s)=1 iff s=5. Terminal outputs indexed by rank:
B: B0(p+2), A2(p+2), A0(p+3), B0(p+6), B0(p+6), A2(p+4).
A: A2(p+2), A0(p+5), A0(p+5), B0(p+6), A0(p+6), B0(p+9).
C: D(p-2), A0(p+5), B0(p+6), A2(p+6), A2(p+6), A0(p+7).

Define D(k) for k>=20 by h=k+8,n=floor(k/6),s=k%6:
- h odd: termB(2h+2+5n,s).
- h even: termB(2h+11+5(n+carry(s)-2),next(s)).

The return maps are:
- A2(p): D(p-4).
- A0(p): put n=floor((p-5)/6),s=(p-5)%6. If p even, termC(2p+6+5n,s). If p odd, termC(2p+15+5(n+carry(s)-2),next(s)).
- B0(p): put n=floor((p-3)/6),s=(p-3)%6,n'=n+carry(s)-1,s'=next(s). If p odd, termA(2p+6+5n',s'). If p even, termA(2p+15+5(n'+carry(s')-2),next(s')).

All outputs have exponent at least 2p. Raw14086Arithmetic.lean proves this and the required lower bounds on triplet counts; kernel axiom profiles only propext, Quot.sound, Classical.choice. Initial exponent 39; by induction every return is applicable. All paths below are positive finite runs using the partial table, hence the blank run is infinite and never queries F1. The conclusion applies to each of the 25 possible F1 completions. This is a paper derivation, not a claim of accepted source Lean closure.

## Derivation

Use exact common-table laws in Raw140DoubleCore.lean, Raw140DoubleGrowthProof.md, Raw140ERBankProof.md, Raw140ERExit.lean, and the counter laws of Raw14042Counter.md. Those laws avoid A1/F0/F1. The variant-specific local identities are checked by the accompanying affine replay, with p-dependent sweeps verified symbolically and opaque contexts never read.

D(k) starts DL(6^k4,4^8 62). The common dIter law gives DL(4,4^h(644)^n s_B). dEndE yields E(1,h-1,Z) where E(a,b,Z)=DL(empty,4^a6 4^b Z), Z=(644)^n s_B. If h odd, eEven yields BR(5^(2h+2),Z). If h even, eIter reaches E(2h-3,1,Z); eOddLast with Z=64 W s_B and W=4(644)^(n-1) gives DL(empty,4^(2h+4)(644)^(n-1+carry(s))rho(s)). convert2 consumes the first 6, giving BR(5^(2h+7),44(644)^(n-2+carry(s))rho(s)); bFour consumes 44 and adds four 5 blocks. bPump removes each remaining 644 and adds five 5 blocks. Apply the terminal B map. n>=3 throughout the initial D phase, so no negative exponents. aSeed takes A2(p) to D(p-4); cSeed takes the rank-zero C terminal to D(p-2).

A0(p): seedCounter with X=3^(p-7)2 gives ER(27 X,3 2^7 31). Repeat the common counterStep p-7 times to obtain ER(272,3 2^p(322)^floor((p-7)/6)s_C), rank (p-7)%6. Deplete the 7 marker: scanTwo, scanTrip, prep, backAll, then finishZero BL(72,22Y)->ER(26,32Y). A further scan/prep/back and final BL6 sweep give BL(empty,2^(p+4)(322)^n s_C), n=floor((p-5)/6),rank (p-5)%6. cInit then cOddPump consumes pairs of twos. If p even the resulting AR left exponent is 2p+6 and right is 2(322)^n s_C. If p odd the exponent m=2p+4 and right is 22(322)^n s_C. cOddStart converts it to ER(2 6^(m+2)4,3 2^2(322)^(n-1)s_C). scanTwo(2), scanTrip(n-1), prep, backAll give BL(6^(m+2)4,2^4(322)^(n-1+carry(s))rho(s)). cOddFinish consumes another 322 and cOddPump yields AR(3^(m+11)2,2(322)^(n-2+carry(s))rho(s)). In either parity cPump consumes the remaining triplets, adding five to the exponent each time; terminal C gives the return above.

B0(p): bSeed gives ER(1 333 5^(p-4),152). The common ER bank law, applied p-4 times, gives ER(1(133)^n 3^(p-1),s_A), n=floor((p-3)/6), rank (p-3)%6. The six suffix prep paths and pumpAny from the depleted-bank exit argument give ER(3^(p+2),1115(115)^(n-2+carry(s))rho(s)). Here there is no terminal 2: the proof uses the arbitrary opaque left context, and stops before the final homogeneous exit. oddInit gives ER(2,1^(p+2)5(115)^n' s'), n'=n-1+carry(s),s'=next(s). oddStart reaches AR(3332,0 1^p5(115)^n' s'). oddPump consumes pairs of ones. If p odd, left exponent 2p+1 and right 015(115)^n' s'; oddLow adds five, leaving the triplets. If p even, exponent m=2p+3 and right 05(115)^n' s'; evenLow gives ER(1 3^(m+1)2,(115)^n' s'); erMany inserts (133)^n'. The common depleted-bank exit (Raw140ERBankProof.md) gives AR(3^(m+12)2,(115)^(n'-2+carry(s'))rho(s')). aPump consumes each triplet adding five, then terminal A gives the stated return. n'>=2 from p>=24.

## Evidence boundaries

The primitive root replay and all 34 variant-local paths were checked; an independent accelerated section simulator also matched the entire arithmetic return for 108 cases (all three section kinds, exponents 24 through 59). The latter is a regression check, not the proof of the unbounded statement. The symbolic paths and inductive common rules are the paper proof. Remaining tasks: compile the exact original-source local-rule bank, compose the common phases and seed in Lean, obtain NeverHalts and weighted Cover, and consume the exact leaf in the Raw140 three-hole cut. Sibling 36's existing exact source bridge is separate. Do not subtract either from the parent or canonical roster before checked composition.
