# Raw139 earlier siblings and C/1=0LC expanding sweep

Nine newly identified side-cycle candidates close entire depth-2 and depth-3 siblings: E/0 = 0LE,1LE; D/0 = 0LC,1LC,0LD,0RD,1LD,0LE,1LE. Two explicit two-state FAR witnesses close the depth-4 C/1 = 1RC and 1RE siblings. These 11 disjoint cylinders contain 2*25^6 + 7*25^5 + 2*25^4 = 557,421,875 completions. They are absent from the earlier 38-entry side-witness bank. The exact Lean source candidates are in EarlySiblingCover.lean; source audit and frontier integration are pending.

A separate depth-4 C/1=0LC subtree search left one unresolved one-hole table, `1RB0RF_1RC---_1LD0LC_1RA0LE_0LD1RC_1LD0RA`. The unassigned B/1 row never needs to be read. In the head-inclusive-left zipper, define A(n) as state A with left [1,1] and right 0^n 1. The blank computation reaches A(4) after 17 ordinary moves. For all n, 3n moves fill the zero interval, 13 moves turn into state C with n+5 ones to erase, n+5 moves erase those ones, and two moves restart at A(n+5). Hence A(n) -> A(n+5) in exactly 4n+20 moves, giving an unbounded live blank-start execution for every completion of B/1. C1Sweep.lean proves the arbitrary-width recurrence; the recurrence and entry compiled locally against copied exact zipper definitions with Lean 4.36.0-rc2. The original source bridge awaits CI. This resolves the mathematical obstruction in the C/1=0LC subtree; the complete parent certificate still needs assembly and exact source audit. No exact BB(6) claim.

## Exact-source Lean verification

The nine side-cylinder, two FAR-cylinder, and unbounded C1Sweep theorems passed the Lean 4.36.0-rc2 closure and axiom audit in [run 45556284591](https://github.com/FlareZ123/bb6/actions/runs/45556284591).

The C/1=0LC subtree assembly is in `C1ZeroLCCover.lean`: 51 first-hole splits, 988 side-cycle leaves, six 1-state FAR leaves, 179 last-hole leaves, and one unbounded sweep leaf (1,225 ordinary-tree nodes). The largest finite first-hole time is 315, yielding a conservative uniform weighted bound 321. Every split includes the halt case. The complete assembly is awaiting the expanded workflow audit; the source is committed, not yet verified.
