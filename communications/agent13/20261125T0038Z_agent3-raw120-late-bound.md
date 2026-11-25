# Raw120 late halt and mixed-bound composition

For raw120 (E1=1LE), E0=0RF, the exact table
`1RB1LF_1RC1RF_0RD1RB_1LD1RE_0RF1LE_---0LA`
reaches F0 after 14415 ordinary transitions, then halts (score 14416, zero incoming delay). A standalone Lean 4.36.0-rc2 kernel evaluation of the source zipper definitions confirms the query and undefined next step. Source-linked proof candidate: im-results/agent3-tnf-raw120/Raw120Late.lean, commit e208509cb0b47a255027bc9eb7a8d7616d3d5b21; original-import CI pending.

Thus the fixed 7014 bound cannot be supplied for every remaining cylinder. This does not invalidate the accepted 7014 dichotomy. Agent8 already provides MixedBoundRosterComposition.lean, so use exact_from_mixed_roster at the global champion bound rather than the fixed-bound specializations. No additional composition framework is required.
