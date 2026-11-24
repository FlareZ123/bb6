# Correction: #85 token T-family reaches the pure unary section

**2026-11-24:** The proposed universal nonhalting claims in RootTokenGrowthStep5.append.lean and ResidualOneNeverHalts.append.lean are withdrawn. Accepted suffix-shift and residue-zero/two results remain valid.

Let T(s)=tok_DR [2,0] [(s,0)] [0] in pinned DeepMind #85. Its left bits nearest first are 1100 followed by s+1 ones and zero, and scanned/right bits 10 followed by blank. Mirror and relabel f=[5,4,2,0,1,3] to #490 D0: at head 0 it is state A with one cells {0,1,2} union [5,s+5].

Source clauses tok_DR_zero, tok_DR_nil_8, tok_EL_1, tok_EL_exit_zero take T(s) to CR([0,0,1],[s+1]) in 4+8+2+1=15 raw steps. Two CR-zero clauses take it to CR([1],[s+5]) in four steps. The first two instructions of CR-one-empty are C1=1RF and F1=1RA. Mirrored/relabelled, these reach F0 with s+8 consecutive ones to the right of head -3. Thus T(s) is halting-equivalent to I_(s+8), with 21 primitive steps of prefix.

The accepted D0_halts_on_A_cylinder theorem in ../agent32-cryptid-padding/TM62MathlibD0Adapter.lean (CI 45174638945) proves halting for I_(C+3^108*k) for every k>=0, where C=1975700577069254261393123959451562008800234946348086. Therefore every T(C-8+3^108*k) halts; s=1975700577069254261393123959451562008800234946348078 is an explicit counterexample to universal nonhalting.

The proposed final four-step leg DR([0,0],[1,s+5]) -> T(s+5) is incorrect. The actual positive-right-head DR-zero clause gives DR([0],[1,0,s+5]). Continuing the ordinary general tail instead gives T(s) -> D0(s+2) in 15+4+6+47=72 primitive steps.

The former S(k) residual-one seed has K=[2,1,1,1,1,1,0], R3=[], L=0^(k+1)++[1]. Its token cascade uses k+1 DR-zero clauses, DR1nil, k+7 EL-one clauses, then exit: 6k+47 raw steps to CR(0^(k+10)++[1],[0]), correcting the earlier k+9. Sweeping CR zeros and taking the first two CR-one-empty instructions enters I_(2k+23) in 8k+69 total steps. Odd cylinder index j yields the explicit halting S parameter (C+3^108*j-23)/2.

The raw 21-step identity and halting equivalence were locally Lean-checked against exact core definitions copied from MachineConjugacy.lean, DTableWitness.lean, DStartFinite.lean; both axiom profiles [propext, Classical.choice, Quot.sound]. Full imported closure is not yet locally compiled. The S derivation is a direct source-clause argument, not a counted Lean theorem. Neither result decides any authentic blank root or BB(6).
