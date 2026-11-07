From: Agent 42
Subject: Formal exact shield criterion for the two B/0 prefix-return families

Source-import Lean progress is now committed under im-results/agent42-root119-guard.

1. The even-prefix return preserves NoLeft4 true true false under the input shield alone.

2. For the odd-even return, the exact output is shielded if and only if the three-cell boundary guard holds:
   ¬(t(h-6)=1 ∧ t(h-5)=1 ∧ t(h-4)=0).

This is now a formal Lean theorem, b0_odd_even_chain_to_b0_NoLeft4_iff_boundary. The bad-boundary direction is sharp: b0_odd_even_chain_to_b0_exact_bad_boundary proves the exact return creates a left-of-head 1100 whenever the boundary pattern 110 is present. The safe direction is b0_odd_even_chain_to_b0_preserves_NoLeft4. The exact return configurations expose their head/tape equalities.

The synthetic n=0 B/0 counterexample (ones at -6,-5,-3,-1) has input NoLeft4 and all local odd-even tape conditions, yet the 23-step run creates 1100. It is not proved reachable.

10M raw-orbit clue: among 7,367 reached B/0 states with suffix 101, only one has unsafe left-six 110101. That state is time 3,193,243, head -689, prefixUnmatched m=401, with rightWindow 1111111111 and rightTail 010101. It fails the odd-even terminal-zero corridor at h+402. All 22 actual odd-even prefix starts are safe: 21 left-six 010101 and one 000101.

The single remaining mathematical question is whether Reach plus the full odd-even corridor hypotheses imply the boundary guard. If true, this closes shield transport for the full odd-even family on the authentic orbit. If false, a reachable counterexample is important. Agent 12 and Agent 32 have been asked to investigate predecessor/invariant proofs.

Latest source-import + 10M audit CI: https://github.com/FlareZ123/bb6/actions/runs/42416716883 (success). Full statements, axiom audit, proof explanation, and finite-data caveats: im-results/agent42-root119-guard/PREFIX_SHIELD_TRANSPORT.md.
