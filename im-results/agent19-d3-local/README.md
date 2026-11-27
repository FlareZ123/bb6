# D3 local first-hole refinement (source acceptance pending)

Parent: `1RB0LC_1RC---_1LA0LD_0RB---_------_------`, at raw13 relative address A1=0LC, C1=0LD, D0=0RB. The actual D3 leaf is `1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---`.

The old Agent46Raw13Ingest77 descendant filter erroneously used tableOK (equality), which cannot match a six-hole cylinder to an eleven-row leaf. It now uses parentCheck on the actual D3 machine. Original source acceptance of the edited module is pending; the previously accepted 77-entry theorem is not affected.

The exact D3 path splits B1@11, E0@12, E1@14, F0@15, D1@23. Quotient cut is 4,5,5,6,6. Of 111 sibling cylinders, 29 translated-cycle candidates, five last-hole candidates and three new symbolic-pumping candidates are closed in the proposed cut. Retains 74 other cylinders plus D3, total 75; weighted open mass candidate 181508275. The implicit halt children are handled by the original weighted first-hole checker. No halting/nonhalting claim for D3 is made.

New affine families from authentic blank prefixes:
* D1=0LB: at 132 steps, A on blank with empty left and right 10100 1^(9+4n); period 48n+143, n -> n+1.
* D1=0RB: at 35 steps, A blank, empty left, right (101)^(3+4n); period 80n+118, n -> n+1.
* D1=1RC: at 10 steps, marked(0,0). Marked(i,j) is A blank, right (10)^(i+1) 11 (01)^j; plain(i) is right (10)^(i+1) 1. The four exact positive-cost symbolic transitions are marked(i,j+2) -> marked(i+3,j) and marked(i,1) -> plain(i+3) at 6i+22, marked(i,0) -> marked(0,i+3) at 6i+26, plain(i) -> marked(0,i+2) at 6i+22. This invariant is closed for every natural i,j and avoids F1. These are candidate proof terms with parametric sweeps, not a bounded simulation inference.

D3LocalPumps.lean uses the original Auto and Auto2 sweep checkers; D3LocalCut.lean combines them with existing translated-cycle/last-hole checkers, proves conditional local and generic graft soundness when compiled. remaining.json is a candidate exact residual list (the kernel theorem is authoritative). The cut is intentionally separate from the large generated Raw13Data closure. D1=1RD and 0RE remain unresolved; 0RE and D3 show matching sampled boundary trajectories but no equivalence is proved.

Run existing workflow agent19-raw77-proof.yml target d3-local with exact source_revision. Do not treat the counts or three candidates as accepted until CI/Lean succeeds. No global roster count reduction is claimed.
