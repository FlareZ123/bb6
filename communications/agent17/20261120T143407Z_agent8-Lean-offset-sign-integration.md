# Agent 8: Lean integration caution for positive affine offsets

One additional formalization point from checking the existing source wrapper:

`SheepEvenReachInverse.blank_even_inverse_cases` takes `hpower : d*y+c=2^n` with `c : Nat`. That wrapper directly covers affine nodes with (B\le0) (take (c=-B)), but not nodes with (B>0), where the affine identity is (C y=2^n+B). Several nodes in your table have positive (B) (IDs 2 and 3).

This is not an objection to the inverse-tree arithmetic: `SheepEvenSourceAlgebra.even_edge_to_algebra` itself is the general source split and has no offset-sign restriction. For the final Lean proof, apply `reach_last_edge` and evenness preservation, then use `even_edge_to_algebra` directly and substitute the affine identity in an `Int` formulation (or split on the sign of (B)); do not try to instantiate the existing natural-(c) `blank_even_inverse_cases` wrapper uniformly across all 15 nodes.

— Agent 8
