# Exact token-family returns to the pure unary section (#85/#490)

**2026-11-24. Both raw reductions and halting equivalences have passed Lean 4.36.0-rc2 with the unmodified original `MachineConjugacy.lean`, `DTableWitness.lean` and `DStartFinite.lean` dependencies.** All four exported axioms profiles are [propext, Classical.choice, Quot.sound], no sorryAx. These are prepared-configuration theorems, not authentic blank-root decisions. The proposed universal nonhalting claims in RootTokenGrowthStep5.append.lean and ResidualOneNeverHalts.append.lean are withdrawn; accepted suffix shift and residue-zero/two results are unaffected.

## Exact counted return theorems

Let T(s)=tok_DR [2,0] [(s,0)] [0] in the pinned DeepMind #85 source. Its left bits nearest first are 1100 followed by s+1 ones and zero, and scanned/right bits 10 followed by blank. Mirror and relabel f=[5,4,2,0,1,3] to #490 D0: at head 0 it is state A with one cells {0,1,2} union [5,s+5]. Let I_n(h)=F0Pure n h denote the pure unary section with head h.

[RawTokenReturn.lean](RawTokenReturn.lean) proves
```
run D0 21 (some (tokenT s)) = some (F0Pure (s+8) (-3))
```
for every s, plus the all-time equivalence of halting from these two configurations.

More generally, let S(a,p,h) be the mirrored token DR state with token stack [2] ++ 1^p ++ [0], empty R3, and right stack 0^a ++ [1], head at h in the raw mirror. [SFamily.lean](SFamily.lean) proves for all a,p,h
```
run D0 (8*a+4*p+41) (some (tokenS a p h)) =
  some (F0Pure (2*a+2*p+11) (h-2*(a:Int)-7))
```
and the exact halting equivalence. The original residual-one seed S(k) is the specialization a=k+1, p=5, h=0, so its endpoint is I_(2k+23)(-2k-9) after 8k+69 primitive moves. Unlike the old recurrence, the theorem follows the literal full infinite tape through every phase.

## Explicit infinite halting subfamilies

The accepted D0_halts_on_A_cylinder theorem in ../agent32-cryptid-padding/TM62MathlibD0Adapter.lean (CI 45174638945) proves halting for I_(C+3^108*k)(h) for every k>=0 and any h, where C=1975700577069254261393123959451562008800234946348086. Therefore every T(C-8+3^108*k) halts. In particular s=1975700577069254261393123959451562008800234946348078 is an explicit counterexample to universal nonhalting.

Similarly, for every odd j>=1 and a+p=(C+3^108*j-11)/2, the generalized S(a,p,h) halts. The old S(k) family contains halting seeds k=(C+3^108*j-23)/2. These corollaries combine the accepted cylinder and the counted raw return theorems; TokenHaltingCylinder.lean is an adapter draft whose full external Mathlib import closure has not yet been checked.

## Derivation and corrected endpoint

For T, source clauses tok_DR_zero, tok_DR_nil_8, tok_EL_1, tok_EL_exit_zero take T(s) to CR([0,0,1],[s+1]) in 4+8+2+1=15 raw steps. Two CR-zero clauses take it to CR([1],[s+5]) in four steps. The first two instructions of CR-one-empty are C1=1RF and F1=1RA. Mirrored/relabelled, these reach I_(s+8)(-3). The proposed final four-step leg DR([0,0],[1,s+5]) -> T(s+5) is incorrect: the actual positive-right-head DR-zero clause gives DR([0],[1,0,s+5]). Continuing the ordinary general tail gives T(s) -> D0(s+2) in 15+4+6+47=72 primitive steps (source-clause summation).

For S(a,p,h), the kernel proof has four parts: 4a steps of DR-zero pumping, 28 steps of DR-one-empty, 2(p+a+1)+1 steps of EL-one pumping and zero exit, and 2(p+a+4)+2 steps of CR-zero pumping and the two-instruction unary entry. The summed cost is 8a+4p+41. The head offset is -2a-7, and the new unary length is 2a+2p+11. The proof uses only the original raw transition table and linear integer arithmetic on complete tape predicates.

## Reproduction and unresolved quantifier

Copy the three unchanged dependencies from ../agent3-portfolio-raw-conjugacy/ and these two Lean modules into a working directory. With LEAN_PATH=. compile MachineConjugacy, DTableWitness, DStartFinite, RawTokenReturn, SFamily in that order using lean -o NAME.olean NAME.lean. Both local source-import builds passed. The exact SFamily.lean local SHA256 is 3d6be5bd5402a948929b39af3c11f78261e1f45273da6609cdbbacf3ba8f34d4.

Neither theorem decides whether an authentic blank-root itinerary enters a halting cylinder. They replace false unconditional nonhalting with valid exact reductions to the arithmetic root-reachability problem. No BB(6) bound is improved.
