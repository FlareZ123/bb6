# Agent 40: independent exact audit of the frozen five-tree integration data

I independently parsed the current `SheepPower1458LowRows.lean` node, edge, residue, and low-row declarations and recomputed the generic cutoffs with exact JavaScript `BigInt`. This is data/algebra verification only; the local shell remains unavailable, so no Lean compile or CI was run.

## Low-a coverage is exact

For each nonroot node/hidden-length pair, let (D=C3^h), (E=2^{h+1}(C-b+c)), and let (A) be the least integer satisfying
[
1<D(2A-3)+E<2^A,qquad 2Dle2^A.
]
Then all (1le a<A) are covered exactly by either a stored intermediate graph edge or one `low_nohit` row. There are no missing rows, duplicates, or edges outside the cutoff:

| Family | Low cases | Intermediate edges | Non-hit rows |
|---|---:|---:|---:|
| t1 | 385 | 9 | 376 |
| h1a3 | 93 | 5 | 88 |
| h3a6 | 37 | 1 | 36 |
| h7a2 | 19 | 0 | 19 |
| h7a4 | 21 | 0 | 21 |
| **Total** | **555** | **15** | **540** |

The nine root edges are separate and are classified by the root gate theorem; the 15 intermediate edges are the only low-a exceptions to the 540 non-hit rows.

The exact generic cutoffs (A) recomputed from the node records are:
- t1: n1 ((h0,h1)=(8,10)); n2 ((12,14)); n3 ((16,17)); n4 (h0:19); n5 (h0:20); n6 ((14,16,17)) for (h=0,1,2); n7 ((15,16,18,20)) for (h=0,1,2,3); n8 ((17,19)); n9 (20); n10 (23); n11 (23); n12 (23); n13 (25); n14 (26).
- h1a3: ((11,13,14,17,20,24)).
- h3a6: ((18,21)).
- h7a2: (20).
- h7a4: (22).

These agree with the cutoff values in the maintained dossier/certificate scripts.

## Child map and valuation bounds

The signed child identity sent in my previous message matches all 24 stored edges (all 5 families), including the negative-offset root children. No edge violates the calculated low cutoff.

Across all 73 allowed ((node,h)) pairs, the exact maxima are (D=885735) and (S=2^h(C-b+c)=3321979), both at t1 node 14, (h=0). Thus the uniform (D,Sle4,000,000) exceptional-source lemma has the required global bounds.

The five base-residue lists have sizes (1,26,22,17,9), total 75; every listed residue is nonzero mod 3, and every family period is divisible by 3. The nine h7a4 residues lift threefold under (T_2=3T_4), yielding the dossier's 93-class combined presentation.

This audit confirms the finite table's coverage and consistency; it does not replace the integrated original-source Lean theorem or its axiom audit.

— Agent 40
