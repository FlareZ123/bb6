# #429: separated low-side excursion exit theorem

**Result.** A bounded-word theorem for all mixed ordinary words, with an actual accelerator section-return consequence. In the low-side scale regime below, deviations except residues 0 and 18 modulo 27 are guaranteed to return to a section in a number of accelerator steps linear in the scale exponent. For residue 0 the same short-prefix halt exclusion holds, but the bound on section return does not. This is a prepared-state result, not a genuine blank-root decision or BB(6) upper bound.

[BB429CoarseExit.lean](BB429CoarseExit.lean) proves the arithmetic over arbitrary words; [BB429CoarseExitSource.lean](BB429CoarseExitSource.lean) connects it to the exact BB429.next/run equations. Both passed local Lean 4.36.0-rc2 against exact relevant declarations of [BB429Rank](../agent5-429-rank/BB429Rank.lean), with printed axiom profiles for low_no_halt, low_no_full, return_from_separated all exactly [propext, Classical.choice, Quot.sound]. Full unchanged-file CI has not been run. No original raw-TM bridge is asserted here.

## Mechanism

Set U=6u+18, V=6u+3w. A two-step block from odd w, with neither output having first counter 0 or 11, is one of
```
U'=4U,       V'=V+18
U'=4U-2V+54, V'=V+42
U'=4U-2V+6,  V'=V+30
```
Let e=0 for the first kind, 1 otherwise. With U0=aP+x,V0=rP+y, x,y nonnegative, define a_i by a_(i+1)=4a_i-2e_i*r. For L blocks, B=x+2y+84L+54, M=5^L B, induction gives |U_i-a_i P|≤M, 0≤V_i-rP≤M. Separation P>3M+39 and natural-counter physical bounds 18≤U_i≤V_i+18 force 0≤a_i≤r. Halt at an odd-block boundary forces 2U_i=V_i+39, so 2a_i=r. At an intermediate even-w state halt is impossible.

For s≥0 set a=144*16^s-2d, r=216*16^s, L=2s+6. Since a mod27=(9-2d) mod27, and r=0 mod27, halt is impossible within L ordinary blocks whenever d≠18 mod27.

At i=2s+2, write H=8*16^s. The formula a_i=4^i*a+r*q gives a_i=H*z, z=2a+27q. Thus 0≤z≤27; later normalized steps are z'=4z or 4z-54. The only integers in [0,27] admitting four such steps within [0,27] are 0 and 18 (proved by omega). Since z mod27=(18-4d) mod27, either d=18 or d=0 mod27. For other deviations L complete ordinary blocks cannot exist. The source theorem return_from_separated proves a successful return to u=0 or u=11 within 2L=4s+12 macro steps: no return would imply a surviving full ordinary prefix by induction using halt exclusion, and that prefix is impossible.

## Prepared low-side section application (paper composition)

Use Agent6's [low-side cycles](../agent6-harmonic429/BB429LowReturnBand.lean). Let m=j+s, X=16^m, P=16^j, W=72X+d-12m-6, d≥6, d=2 mod4. The F^(4m+3) burst reaches (24X-3,24X+9+d). Assume the exact j-cycle endpoint u satisfies

    3u + dP = 72X-9+d+24j,     u≥5dP+7.

Then the existing cycles theorem reaches (u,u+12+dP) after another 4j steps. The scaled coordinates are exactly U=(144*16^s-2d)P+2d+48j and V=216*16^s P+3d+9+72j, so use x=2d+48j, y=3d+9+72j. If P>3*5^(2s+6)*(x+2y+84*(2s+6)+54)+39 and d mod27∉{0,18}, return_from_separated gives a safe section return within total 8m+15 accelerator steps from (0,W). These substitutions and composition are presently a paper corollary of the source theorem and Agent6's already checked cycles/zero_burst, not yet an integrated Lean statement.

For each fixed d in the 25 allowed classes, choose fixed s with d≤16^s; j=m-s sufficiently large ensures the cycle guard and separation. The endpoint u exists because P≡1 mod3, and exponential P eventually dominates the linear j-dependent budget. Thus this removes the unbounded word-length quantifier for each fixed admissible d at all sufficiently large scales, including genuinely mixed words. It does not establish that blank-root section deviations lie in this regime or avoid the two exceptional classes. For a trajectory-level induction, the returned section value and its deviation at the next scale are still needed.

## Reproduction

Compile unchanged BB429Rank.lean to BB429Rank.olean, then compile BB429CoarseExit.lean to BB429CoarseExit.olean and check BB429CoarseExitSource.lean with LEAN_PATH containing both module directories. No mathlib dependency. Relevant novelty relative to [the fixed-word low-side classification](../agent6-harmonic429/LowSideTerminalClassification.md) is the bounded-word/forced-return result for scale-separated deviations, not a stronger claim about all prepared states. External priority not established.
