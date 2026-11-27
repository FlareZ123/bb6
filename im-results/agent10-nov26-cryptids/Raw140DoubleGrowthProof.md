# Two Raw140 sibling nonhalting proofs by a word-preserving bounce
2026-11-27. **Mathematical derivation, with exhaustive finite local rule checks in JavaScript; Lean integration pending.** This is an all-time argument, not an extrapolation of the earlier return samples. It addresses exactly local IDs 73 and 80:
```
1RB1RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0LB---
1RB1RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---
```
Each missing F1 row is never visited. Every completion of that row is therefore nonhalting. The two 25-completion cylinders are distinct, conditional on the repository's usual 25-option normalization. No claim about the entire raw140 tree or global Canonical58 roster follows until exact composition.

## Conventions and finite entry
A block is 3 tape bits, little endian (S 0,...,S 7). At a block boundary, QR(L,R) enters the first right block at its low end; QL(L,R) enters the first left block at its high end. Both stacks are nearest first, implicit infinite zero tail. Concatenation is juxtaposition, empty word ε. A block arrow `QRx -> PLy` means entry at block x, exit to the left in state P, leaving y; the exiting direction determines the new stack location. This is exactly Raw140Orbit.boundary and stepR/stepL.

Set T(m,n,s)=BR(5^m,(644)^n s), with m even >=18, n>=2, and s in S={62,64,6221,6421,6405,62542}. Exact blank-tape simulation enters T(32,1,64) at time 5985 (2077 individual 3-cell exits after primitive time 2), then:
- 0LB: T(78,5,62) at 42133.
- 0RD: T(80,5,6221) at 44429.
Raw140DoubleGrowth.js computes these entries without supplying F1. All subsequent work is unbounded symbolic, so only this finite entry requires a finite trace.

## Local laws
For the common nine-row base table with A1,F0,F1 undefined, the following finite local paths are sufficient. X,Y arbitrary stacks, b∈{4,6}; cost is in primitive steps. A sequence lists the successive entered blocks (state, direction, block), not merely a sample trajectory. The expressions hold even for empty contexts; no arbitrary context is read. The finitely many block exits can be verified from the table by following at most 145 primitive steps inside each block, as in BlockMacro.

| Input | Output | Cost | Entered blocks |
|---|---|---:|---|
| CR(4X,4bY) | CR(45X,bY) | 19 | CR4 DL4 ER6 BL1 CR6 ERb BL0 |
| CR(4X,6bY) | CR(44X,bY) | 7 | CR6 ERb BL0 |
| DL(6X,bY) | CR(4X,bY) | 5 | DL6 ERb BL0 |
| DL(55X,Y) | DL(5X,4Y) | 3 | DL5 |
| DL(54X,Y) | DL(5X,6Y) | 15 | DL5 DL4 ER4 BL1 CR4 |
| DL(4,4Y) | DL(ε,46Y) | 15 | DL4 ER4 BL1 CR4 DL5 |
| BR(5X,44Y) | DL(55X,6Y) | 10 | BR4 ER4 BL1 CR4 |
| BR(5X,464Y) | CR(455X,4Y) | 14 | BR4 ER6 BL1 CR6 ER4 BL0 |
| CR(X,64Y) | CR(4X,4Y) | 7 | CR6 ER4 BL0 |

The finite suffix laws CR(4X,s) -> DL(5X, (644)^c rho(s)) are:

| s | rho(s) | c | cost | entered blocks |
|---|---|---:|---:|---|
|62|64|0|45|CR6 ER2 BL0 CR2 DR0 BL6 BL4 BR2 BR1 DL5 DL5 DL4 ER4 BL1 CR4|
|64|6221|0|67|CR6 ER4 BL0 CR4 DL4 ER6 BL1 CR6 ER0 BL0 CR0 DL4 ER2 BL1 CR2 DR0 BL6 BL5 DL5 DL4 ER4 BL1 CR4|
|6221|6421|0|45|CR6 ER2 BL0 CR2 DR2 BL6 BL4 BR2 BR3 DL5 DL5 DL4 ER4 BL1 CR4|
|6421|6405|0|69|CR6 ER4 BL0 CR4 DL4 ER6 BL1 CR6 ER2 BL0 CR2 DR1 EL6 ER1 EL2 BL4 BR1 DL5 DL5 DL4 ER4 BL1 CR4|
|6405|62542|0|83|CR6 ER4 BL0 CR4 DL4 ER6 BL1 CR6 ER0 BL0 CR0 DL4 ER2 BL1 CR2 DR5 EL6 ER5 ER0 BL1 CR0 DL5 DL2 BL5 DL5 DL4 ER4 BL1 CR4|
|62542|62|1|55|CR6 ER2 BL0 CR2 DR5 EL6 ER5 ER4 BL1 CR4 DL5 DL2 BL4 BR5 DL5 DL4 ER4 BL1 CR4|

These paths were actually checked with A1,F0,F1 all absent and marker X inaccessible. The right blank is implicit, not an arbitrary context.

### Word-preserving bounce
For every finite W∈{4,6}*, arbitrary X and any suffix s∈S,
```
CR(4X, W s) -> DL(5X, W (644)^c(s) rho(s))
```
in exactly 22|W|+cost(s) primitive steps. Proof by induction on W. Empty uses the suffix table. If W=aV, then the first letter of V s is 4 or 6. For a=4, use forward4, induction with X'=5X, reverse4, yielding cost 19+22|V|+cost(s)+3. For a=6, use forward6, induction with X'=4X, reverse6, yielding 7+22|V|+cost(s)+15. The reverse laws impose no constraint on the output stack. Hence the entire arbitrary word is preserved, not just its length.

Combining DL6 lift, the bounce and one DL5 gives
```
DL(6X,W s) -> DL(X,4 W (644)^c(s) rho(s))
```
with cost 8+22|W|+cost(s). By induction over k, if j suffix rotations from s add C_j(s) copies of 644 and have final suffix rho^j(s), then
```
DL(6^k X, W s) -> DL(X,4^k W (644)^C_k(s) rho^k(s)).
```
The six-cycle has exactly one carry, from 62542 to 62. Set rank(62,64,6221,6421,6405,62542)=0,1,2,3,4,5. Then 6 C_j(s)+rank(rho^j(s))=j+rank(s), by induction. In particular C_j(s)=floor((j+rank(s))/6) and C_j(s)>=floor(j/6).

## Two homogeneous conversions
For any p>=0 and arbitrary W:
```
DL(5^p,2W) -> CR(6^(p+2)4,W), cost 12p+16.
```
The entered blocks, with repeated groups abbreviated, are DL5^p DL0 AR4^p AR2 EL3^p EL2 BL0 CR1^(p+2). These are ordinary same-state sweeps. The tape after AR2 is EL(3^p2,1W); after EL2, BL(ε,1^(p+2)W). Both are exact.

For a>=0 and arbitrary Z:
```
DL(ε,4^a6Z) -> BR(5^(a+3),Z), cost 15a+32.
```
Entered blocks DL0 AR4^a AR6 EL3^a EL2 BL0 CR1^(a+1) CR5 BL6^(a+1) BL4 BR2^(a+2). For example after CR5 the state is BL(6^(a+1)4,2Z); after BL4 it is BR(5,2^(a+2)Z). This proves the conversion for every Z, not just even words.

Abbreviate E(a,b,Z)=DL(ε,4^a6 4^b Z). For b>=2, the latter conversion followed by the BR two-four law and a DL5 sweep gives
```
E(a,b,Z) -> E(a+4,b-2,Z), cost 18a+54.
```
Therefore E(a,2j,Z) reaches BR(5^(a+4j+3),Z); E(a,2j+1,Z) reaches E(a+4j,1,Z). No restriction on Z.

## The 0LB return
Start T(m,n,s), m even >=18, n>=2. Put p=m. The three entered blocks BR6 FR4 BL5 use 7 primitive steps and give DL(5^p,2 44 (644)^(n-1)s). Apply homogeneous conversion; then CR4 gives
```
DL(6^(p+2)4,64 (644)^(n-1)s).
```
Apply k=p+2 iterations of the DL6 bounce. Write r=n-1+C_k(s) and t=rho^k(s). The result is DL(4,4^(p+2)64(644)^r t). Apply the DL(4,4Y) law:
```
E(1,p+1,64(644)^r t).
```
Since p is even, p/2 E-iterations give E(a,1,64(644)^r t), a=2p+1. Apply homogeneous conversion to get BR(5^(a+3),464(644)^r t). Apply the BR one-four law (take X=5^(a+2)):
```
CR(4 5^(a+4),4(644)^r t).
```
Bounce on W=4(644)^r and sweep DL5 exactly a+5 times:
```
DL(ε,4^(a+6)(644)^r' t'),  r'=r+c(t), t'=rho(t).
```
Here r'=n-1+C_(p+3)(s)>=1. Rewrite as E(a+6,2,(644)^(r'-1)t'), apply one E-iteration and then the even-E conversion with b=0. This reaches
```
T(2m+14, n-2+C_(m+3)(s), rho^(m+3)(s)).
```
The n expression is at least n+1 because m>=18. All paths are finite, positive, and use no F1.

## The 0RD return
Start T(m,n,s), m even >=18, n>=2; put p=m+2. The five entered blocks BR6 FR4 FR4 FR6 BL5 use 19 primitive steps and give DL(5^p,2(644)^(n-1)s). This reset requires n>=2, satisfied after the explicitly checked entry. Homogeneous conversion followed by the CR(X,64Y) law gives
```
CR(4 6^(p+2)4,44(644)^(n-2)s).
```
Bounce on W=44(644)^(n-2) and sweep one DL5, yielding
```
DL(6^(p+2)4,444(644)^(n-2+c(s))rho(s)).
```
Apply k=p+2 DL6 bounces. Write r=n-2+C_(p+3)(s), t=rho^(p+3)(s). Result DL(4,4^(p+5)(644)^r t). Apply the DL(4,4Y) law:
```
E(1,p+4,(644)^r t).
```
Since p is even, the even-E conversion reaches BR(5^(2p+12),(644)^r t), i.e.
```
T(2m+16, n-2+C_(m+5)(s), rho^(m+5)(s)).
```
Again n' >= n+1, no F1, positive time.

## Conclusion
Both returns preserve m even >=18 and n>=2, and have positive step count. Starting at the finite verified entries, iterating the proved return rules gives arbitrarily long prefixes of the deterministic blank execution. Thus neither machine ever halts or queries F1. This proves their nonhalting, subject only to the explicitly finite root trace and local table checks; Lean acceptance is a separate task. The six-suffix empirical table in Raw140DoubleGrowth.md is a consequence of this rotation formula, not an assumption.

## Formalization plan
Reuse Raw140OrbitCore.stepR/stepL/sweepR/sweepL and Raw140ExtraCore.run_ext. Prove the local rules using the listed exact paths, the word bounce by induction on Bool lists, DL6 iteration by induction, E by induction, and finite entries using Raw140Orbit.execute_sound or Raw140Sweep.execute_sound. Then export `forever` and the two exact weighted Covers via BlockFARBridge.transfer_never. Do not change the roster until those Covers are composed into the exact authentic parent.
