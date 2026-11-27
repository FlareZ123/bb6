# Inductive primary guard for secondary countdowns

Conditional family theorem, strengthening BoundaryEpoch.md; no all-time F421 verdict.

In far-to-near order, let B_i=2^i, M=2^m for m regular cells. Require a=2M-1,b=3M-1. Fix a nonempty far suffix of s cells. For k remaining secondary cycles require suffix p_i >= 2B_i*k+3 and q_i >= B_i+2. For all nearer cells require positive p_i divisible by 2B_i and q_i >= B_i+2. The independent secondary-tail guards still apply.

At A, mark all cells and decrement p by 1. The all-marked budget p_i-1 >= 2B_i-1 holds even at equality, so every cell contributes B_i terminal visits and A drain has M-1 macros. After A subtract 2B_i from each p_i and add B_i to q_i. Delete zero-p cells and merge their q masses into the next nearer surviving q or leading b. All survivors have p_A>=3: by budget for suffix, and divisibility (B_i>=2) for head. Let D=2^(number of survivors), C_i their new positional scales. C_i divides B_i. After A, a_A=a+2M, b_A=b+M+r, where r is deleted Q mass merged at head; each q_A>=q_i+B_i>=2C_i+2.

B crossing swaps run lengths and produces one extra marked far cell and an untouched unmarked (1,y-1). The B marked p lengths are the old q_A and b_A, with drain budgets respectively 2C_i-1 and 2D-1. Thus all B p survive with at least 3; B drain has 2D-1 macros. Its far marked q becomes x-1 and later moves into the exceptional tail, so no dependence on x for the primary endpoint. C crossing swaps back. The old p_A>=3 makes q_B=p_A-1+2C_i sufficient for the C marked budget at doubled scale. The new nearest marked p before C drain is a_A+2D, also sufficient. No C deletions; C drain has 2D-1 macros.

After the three boundaries and drains:
- a'=4D-1,b'=6D-1; M'=2D.
- old survivors p'=p_i-2B_i, q'=q_i+B_i+merged-C_i.
- new nearest cell p'=4M,q'=4M-1+r-D.
- exact principal macro count M+4D.

The fixed far suffix has C_i=B_i and no merged q masses, so q is unchanged. Its budget decreases by one. Every surviving head p remains a positive multiple of 2C_i, and q'>=C_i+2. The new head p is divisible by 2D since D divides M; its q'>=D+2 because D>=2,M>=D. Induct on k. The normalized head lifetime l_i=p_i/(2B_i) deletes l=1 simultaneously; survivors update to (l-1)*2^(number of deleted farther cells), and the new near cell has life 2^(d+1) with d total deletions.

At odd190 the authentic m=10 prefix has M=1024, a=2047,b=3071. The two far cells p=2883545 at scale 1 and p=7077811 at scale 2 suffice for k=32750. All nearer cells satisfy divisibility and all q meet the bounds. Thus the prior guard checks across the full S=32750 secondary countdown have an inductive proof. This does not give a permanent suffix budget.

## Lean status

PrimaryGuard.lean proves cellCount, survivorGuard, reduceGood, advanceHeadGood, iterateHeadGood and suffixBudget. F421Regular.lean proves exact evenReturn and principalEven. F421Drain.lean proves carryAcross and allMarkedDrain (arbitrary all-marked cell count under positional budgets, terminal zero residual P allowed). F421Odd.lean proves exact principalOddE and principalOddD for arbitrary regular and twisted lower segments. All compiled locally in Lean 4.36.0-rc2, the execution modules against reconstructed identical relative-machine definitions and frontier-return proof. Original repository import closure audited separately. No sorry or native_decide. Full composition linking normalization and guard arithmetic to the secondary trajectory remains paper-level; the post-zero boundary remains open.

## Generalized source-level secondary epoch

`F421SecondaryGuard.lean` uses per-row disjunction P≥2Bk+3 or (B≥2 and P a positive multiple of 2B), rather than a fixed protected-prefix split. `sDrainA` proves the exact full horizon with deletion only at P=2B, preserves mixed guard at the compressed positional scales, and gives QBudget 2. The original leading b may exceed 3M−1. `F421SecondaryInduction.lean` proves that the two subsequent strict drains restore each surviving P, subtract its new scale from Q, and append P=4M, Q=b+M+r_A−D. The full source-cycle theorem `secondaryPrimaryCycle` closes the primary guard, and `F421SecondaryEpoch.lean` proves `secondaryEpoch` by arbitrary natural countdown induction. The kernel-checked theorem `firstSecondaryEpoch` instantiates the numerical odd190 seed with all 15 tail rows, 32750 decrements, x=1703916, y=262124, leaving x=1671166, y=229374 and all markers zero. The suffix is arbitrary. This remains conditional on reaching the recorded seed. All modules locally checked against genuine source .olean dependencies, standard axioms only. The full subsequent secondary primary guard is still open.

`F421SecondaryExact.lean` strengthens the epoch to an exact computed endpoint: `sNext` and `sIter` give the autonomous primary recurrence, and `sTailFinal` sends each tail row to `(z+counter(suffix)+bit, r-counter(suffix), false)`. `secondaryEpochExact` proves source reachability of that exact endpoint with standard axioms; local original-source closure passes. This facilitates a compressed arithmetic certificate of the first secondary zero boundary.
