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


## Extension: all-class prefix safety and zero-residue exit

`BB429CoarseExitExtended.lean` formalizes the prepared-state composition, the stronger exact phase/error invariant, and the zero-residue escape. It supersedes the earlier exclusion of both 0 and 18 modulo 27. With phase baseline φ=-18 or +6, the defect 3ε−2η stays at least φ, and ordinary non-F blocks multiply the excess by four. F,F creates strict excess when η≥27. For y>153, a halt in the separated prefix is impossible, even for d=18 modulo 27. At the middle index a surviving d=0 modulo 27 trajectory has leading ratio 2/3 and strict positive actual corridor excess. The excess grows geometrically until a section return. `prepared_except18` proves safe return for every d≠18 modulo 27 with d≤16^s, j≥2, the cycle guard and stated separation, within 12m+31 accelerator steps. The other 25 residue classes retain the earlier tighter bound. These are prepared-section statements, not a blank-root proof. Exact relevant source declarations compiled locally with Lean 4.36.0-rc2; the new module's printed axiom audits contain only standard Lean axioms. Full unchanged dependency CI has not been run.


## Exact base-four resonance and complete smallest resonant family

`BB429Resonance.lean` sharpens the sole remaining first-burst exception. Define B_i recursively by B_0=0, B_{i+1}=4B_i+e_i, where e_i=0 for FF and 1 for OE/OO followed by F. Then lead_i=4^i a-2rB_i. For d=2 mod4, surviving leading zero at 2s+2 forces the final two digits 10, and d=18+216C, where C is the base-four complement word of length 2s. Thus the only exceptions to `prepared_nonresonant` (same scale hypotheses as before) lie in a sparse Cantor-type set, not all 18 mod27. The new source theorem bounds return by 12m+31 for every nonresonant d. 

For a second F burst U=aP, V=27*4^I*P+y with y>=27, ordinary U errors are nonpositive. Leading zero is physically impossible and leading ratio 2/3 at index I requires a=18+54B_I. Therefore `return_from_exact_burst` guarantees section return within 2(I+4) if this resonance is excluded and separation holds. In particular a=12 mod24 excludes it, because B_I=0 or 1 mod4.

**Uniform d=18 result:** `d18_all` proves that for every natural m, prepared(m,18) returns safely to a section in at most 12m+15 accelerator steps. For m>=2, after 8m+4 steps its state is exactly (4m+3,72*16^m+16m+26), from which a second F burst gives a=24m+36, hence 12 mod24. For m>=16 use s=floor(m/4), j=m-s; elementary growth bounds discharge all burst and separation conditions. Sixteen small m are explicit kernel-reduced source witnesses. Remaining nonzero Cantor resonances are not classified, and the actual blank-root section trajectory is not yet connected to a closed family. Local Lean 4.36.0-rc2 passed the whole new module with relevant exact source slices and standard axiom profiles; full unchanged dependency CI remains unrun.


## Global section-shell sparsity (all branch words, including arbitrarily late halts)

[BB429SectionEntropy.lean](BB429SectionEntropy.lean) proves a cardinal bound without truncating the possible halting time. For fixed first counter u and initial odd-rank phase after the maximal F burst, compare two starts x<=y in the second counter. On a shared ordinary two-step word e of length i, the rank difference is exactly 3(y-x) and the first-coordinate difference U_x-U_y is 6*word4(e,i)*(y-x). The first bit must be 1 since a double F from a non-F state violates physical bounds. Thus after k+1 blocks the slope magnitude is at least 6*4^k. At rank cap R the diameter of each surviving word fiber is at most floor((R+14(k+1))/(2*4^k)), and only 2^k signatures are possible. For a halting leaf the identical-word equation 2U=V+39 forces x=y; all leaves of depth less than k+1 contribute at most 2^k. The theorem `no_return_cardinality` bounds the entire bad set by 2^k*(floor((R+14(k+1))/(2*4^k))+2), because every failure to return within 2(k+1) transitions either halts before that time or survives the entire prefix. This includes every eventual first-excursion halt.

[BB429SectionShell.lean](BB429SectionShell.lean) gives a global source corollary, `section_shell_bad_bound`: for every n>=3 and fixed section a=0 or11 (in fact every a<=11), the number of W in [4^n,4^(n+1)) with no successful section return in 4n+5 transitions is at most **72*2^n**. The maximal initial F burst lies in an interval of nine integer lengths [2n-5,2n+3]. The two possible odd-rank phases give at most 18 fibers; each has at most 4*2^n bad starts by the postburst bound. Hence the fraction of exceptional inputs tends to zero at least as fast as O(2^-n). This is an unconditional theorem about the original accelerator, covering all possible mixed ordinary words and all future first-excursion halts. It does not give a blank-root decision, and a sparse exceptional set cannot simply be assumed to be avoided by the genuine orbit. The next objective is an exact enumeration of exceptional intervals and root-crossing arithmetic. Local Lean 4.36.0-rc2 compiled both files and all printed axiom profiles were standard; full original-source CI not run.
