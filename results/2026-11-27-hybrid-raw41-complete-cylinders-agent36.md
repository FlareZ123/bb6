# Hybrid FAR–AutoPump classification of fourteen six-state five-hole families

**Status:** Original Lean 4.36.0-rc2 kernel checked, 27 November 2026. These are new universally quantified partial-machine theorems, not the exact value of BB(6).

## Mathematical theorem

For each partial six-state machine p in the table, the original trusted Lean theorem Raw41NewNNN_bound proves: for every concrete total machine m, TNFQuotientCompatible p m implies WeightedBound B m. The bound B is universally valid; no sharpness claim is made.

| Canonical child | Literal five-hole table | Bound B | Lean CI |
|---|---|---:|---|
| 024 | 1RB0LD_1RC1LC_0RD---_1LD1RA_------_------ | 158 | [46083072538](https://github.com/FlareZ123/bb6/actions/runs/46083072538) |
| 081 | 1RB1LB_1RC0LC_0RD---_1LD1RA_------_------ | 89 | [46081314280](https://github.com/FlareZ123/bb6/actions/runs/46081314280) |
| 083 | 1RB1LB_1RC0RA_0RD---_1LD1RA_------_------ | 92 | [46082196856](https://github.com/FlareZ123/bb6/actions/runs/46082196856) |
| 084 | 1RB1LB_1RC0RC_0RD---_1LD1RA_------_------ | 737 | [46082024854](https://github.com/FlareZ123/bb6/actions/runs/46082024854) |
| 088 | 1RB1LB_1RC1LC_0RD---_1LD1RA_------_------ | 41 | [46079654567](https://github.com/FlareZ123/bb6/actions/runs/46079654567) |
| 090 | 1RB1LB_1RC1RC_0RD---_1LD1RA_------_------ | 84 | [46079698523](https://github.com/FlareZ123/bb6/actions/runs/46079698523) |
| 092 | 1RB1LC_1RC---_0RD0LA_1LD1RA_------_------ | 191 | [46082201246](https://github.com/FlareZ123/bb6/actions/runs/46082201246) |
| 099 | 1RB1LC_1RC---_0RD1LB_1LD1RA_------_------ | 96 | [46080372565](https://github.com/FlareZ123/bb6/actions/runs/46080372565) |
| 101 | 1RB1LC_1RC---_0RD1RB_1LD1RA_------_------ | 123 | [46080377587](https://github.com/FlareZ123/bb6/actions/runs/46080377587) |
| 116 | 1RB1LE_1RC---_0RD---_1LD1RA_---1LC_------ | 121 | [46082536169](https://github.com/FlareZ123/bb6/actions/runs/46082536169) |
| 123 | 1RB1RB_1RC0LC_0RD---_1LD1RA_------_------ | 64 | [46079658514](https://github.com/FlareZ123/bb6/actions/runs/46079658514) |
| 125 | 1RB1RB_1RC0RC_0RD---_1LD1RA_------_------ | 1500 | [46080584392](https://github.com/FlareZ123/bb6/actions/runs/46080584392) |
| 128 | 1RB1RB_1RC1LC_0RD---_1LD1RA_------_------ | 130 | [46082766478](https://github.com/FlareZ123/bb6/actions/runs/46082766478) |
| 134 | 1RB1RC_1RC---_0RD1LB_1LD1RA_------_------ | 167 | [46080382170](https://github.com/FlareZ123/bb6/actions/runs/46080382170) |

Each five-hole partial machine permits 25^5 = 9,765,625 total transition-table completions (24 nonhalting choices plus a halting choice per hole). The fourteen distinct canonical query-outcome families cover **136,718,750 distinct physical completions**.

## Hybrid proof strategy

The original Agent47 two-query canonical partition and Agent19 exact finite-prefix enumerator reduce partial-machine halting to finite source-backed trees with 24 nonhalting branches. Existing finite automata and independently reconstructed SMT-synthesized FAR automata prove nonhalting for most open one-hole leaves. In a rare finite delayed case, the checker substitutes the exact last unassigned query: child125 first reaches its remaining E1 slot at step 1,423, giving a source-checked upper bound of 1,500 for all completions.

Other machines exhibit regular but growing tape patterns beyond short finite automata. The original Agent46 autoword inference proposes a finite list of symbolic affine tape sweeps. The source Lean checker Agent46AutoPump.check checks the certificate for all tape-block exponents, and its theorems check_growth and check_never imply infinite execution. These are infinite mathematical proofs, not extrapolations from finite runs. Child084 uses 47 FAR witnesses and 2 AutoPump certificates; child128 uses 89 FAR witnesses and 1 AutoPump; child024 uses 90 FAR witnesses and 1 AutoPump. Child081 requires a separately synthesized eight-state DFA for the last leaf. All checked proof jobs exclude sorryAx and native_decide and report standard Lean axioms only.

Reproduction sources: im-results/agent36-raw41/close_candidate.py, batch_far.py, batch_auto.py, close_auto_batch.py and probe_auto.py; original trusted helpers im-results/agent47-raw41-cut/generate_two.py, gen_children.py and gen_auto.py; original Agent46AutoPump.lean. Fixed AutoPump JSON certificates and FAR codes are under im-results/agent36-raw41/certificates/. GitHub Actions workflows generate each child tree and compile all 24 branches from exact machine semantics. These explicit sources, rather than an untrusted search or simulator result, determine proof acceptance.

## Certified composition and precise frontier

The first eight of these fourteen complete children also compose into the source-accepted Lean theorems afterNewEight_count = 145 and globalNewEight_count = 221, with soundness: every machine compatible with the original Raw41 parent either obeys WeightedBound 1500 or belongs to the remaining 145 child cylinders; every machine compatible with the earlier rooted quotient either obeys WeightedBound 7014 or belongs to the remaining 221 cases. The proof was accepted in [CI 46081590344](https://github.com/FlareZ123/bb6/actions/runs/46081590344), with standard axioms only. These statements are specifically the **Raw41 local 153→145** and **earlier rooted 229→221** reductions. Stronger eleven-, thirteen-, and sixteen-cylinder union modules have been submitted for separate source checking; their improved counts cannot be claimed as theorems until acceptance.

**Limitation:** The newer accepted 40-case global Canonical40 maximality quotient is a different stronger interface. These partial-machine results do not establish coverage of those 40 holdouts, do not provide a universal BB(6) upper bound, and do not determine the exact BB(6) value. The contribution is the independently source-checked classification of fourteen large machine families and a reusable hybrid FAR–AutoPump procedure.
