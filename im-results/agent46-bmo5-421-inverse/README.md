# Exact injective inverse dynamics for BB6 holdout #421 (BMO5-family)

Machine `1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE` (#421, suspect_13). The upstream reduction is [M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE.lean](https://github.com/google-deepmind/cryptids/blob/ced8f9f44f67a167d5ecc03e687b048c67926371/BusyBeaver/BB6/M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE.lean), blob 03828ae956bdb640b73787f42c8511f06274229a. Its high-level initial state is C(3). Cap.eval is the numerical copy of evalD0 with constructor C erased. All local numerical modules were checked by Lean 4.36.0-rc2, standard axioms only. The initial original-source integration run reached the final wrapper but failed on the two triple-rule proofs; see Source acceptance below. No global halting classification claimed.

## Closed bands

Use half-counter x=(a+1)/2 for odd C(a), so blank root x=2. Every successful step stays odd. Put

- c_i=5*2^i-4
- l_i=5*2^i-i-3
- T_i=10*2^i-i-6.

For x>=2 there is a unique i with l_i<=x<l_(i+1). Set r=x-l_i. Then

    0<=r<=c_i:   f(x)=3*r+c_i+7
    r=c_i+1:     halt (x=T_i)
    r=c_i+2:     f(x)=2*c_i+8=10*2^i.

Additionally f(1)=5, f(0)=none. This is exact, not an asymptotic approximation. In particular successful transitions strictly grow the counter, although f is not monotone as a function across all bands.

## Unique inverse

Regular images of band i range from 5*2^i+3 to 20*2^i-9, and are all congruent to 5*2^i mod 3. Bands separated by at least two have disjoint image intervals; adjacent bands have distinct residues. Special images 10*2^i cannot meet any regular image, by the interval bounds and the same-band residue obstruction. They are mutually distinct. The exceptional image 5 is below every other image.

Thus f is injective on defined steps. For a target y, set j=floor(log2(floor(y/5))). Apart from y=5, only bands j and j-1 can supply a predecessor. Test the special image first; otherwise divide y-(c_i+7) by 3 exactly, requiring a nonnegative quotient <=c_i. This is a complete inverse algorithm without searching over all earlier bands.

## Root criterion

Follow the unique inverse until it is undefined. This terminates by strict growth, defining rootOf(y). Then y is reachable from 2 iff rootOf(y)=2. In particular halting is equivalent to existence of i with rootOf(T_i)=2. Since no defined image is divisible by 3, all terminal indices i=4 or 5 mod 6 are excluded. This is an unbounded exclusion, but the other four residue classes remain.

## Files

- Cap.lean: numerical sweep reduction, odd transport base and exact bands.
- CapInverse.lean: growth, injectivity, exact inverse and terminal family.
- CapRoot.lean: transport of the odd numerical map, terminating ancestry, exact rooted criterion and mod-6 terminal exclusion.

Next: exploit the shared dynamics of other BMO5 starting-state variants and derive a uniform obstruction for the remaining terminal family. Do not treat a finite inverse scan as a decision of the machine.


## Shared BMO5 graph: #252, #421 and #754

The upstream #252 (suspect_04) and #754 (suspect_41) modules have the same three-counter transition rules with different blank starts. In the common section (0,1,2n), use x=n+2. The even diagonal sweep of these rules is exactly drain(x-2,1), hence the same f as #421.

| Holdout | Source section | Blank x | Unique ancestry root |
|---|---|---:|---:|
| #421 | C(2x-1) | 2 | 2 |
| #252 | A2(0,1,2(x-2)) | 5 | 1 |
| #754 | B2(0,1,2(x-2)) | 3 | 3 |

CapMulti.lean proves this reduction for the exact three-counter rules, and proves that the three orbits cannot meet. Node 1 has f(1)=5, so the #252 orbit uses ancestry root 1. Each machine halts iff some terminal T_i has its corresponding ancestry root; this is a common search with three distinct goals, **not** a claim of equivalent halting behavior.

The original-source modules for #252 and #754 are pinned at the same commit ced8f9f44f67a167d5ecc03e687b048c67926371, with blobs 4c56373ec8b39c24789775cddcf1641e3e68aa5e and f99faa84c3198e69233ec1c1ca3f466d2bfde559. CapSource.lean imports all three unchanged upstream modules, applies their IsValidAcceleration certificates to the shared section and states the three machine-level iff criteria. Arithmetic modules and the extracted #421 source-copy proof compiled locally.

## Source acceptance

The initial [manual CI run 45363130008](https://github.com/FlareZ123/bb6/actions/runs/45363130008) compiled the pinned original modules and reported the standard-only axiom profile for H421.root_criterion, but the whole wrapper failed because the H252/H754 rules used `rfl` on equation-compiler definitions. The corrected proof uses `simp [next]`, checked locally against the exact upstream numerical definition under Lean 4.36.0-rc2. The full corrected original-source wrapper still requires one focused acceptance run. No halting/nonhalting decision follows from these equivalences.
