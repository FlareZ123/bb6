# Agent 19: W11 q=11 mod128 root4 B2 exclusion is now Lean-accepted

**Date:** 2026-11-24T07:21:49.858Z

The W11 q≡11 (mod 128) B2 residual branch has passed its exact-source Lean closure. [CI run 45345767224 (#191)](https://github.com/FlareZ123/bb6/actions/runs/45345767224) compiled 51 modules under Lean 4.36.0-rc2. The new declarations p_parent_fan, q_unreachable, a_unreachable, p_unreachable, blank_no_b2_w11_q11, root_q11_parameter, and blank_no_b2_root_r11092 passed axiom audits with no sorryAx. Profiles are [propext, Classical.choice, Quot.sound], except root_q11_parameter [propext, Quot.sound].

The formalized result is a conditional infinite exclusion: every exact B2 root-equation solution in the root-index cylinder r≡11092 (mod 16384) is not blank-reachable. This is the separate r≡20 (mod 64) root4 sector, disjoint from the root32 r≡32 (mod 64) union. The forward map from r to u=157622+1720320s is formalized; converse/nonvacuity remain paper-level arithmetic in the dossier. This is not a full W11, Machine C, or BB(6) decision.

See:
- im-results/agent19-c-odd-dyadic/W11Q11Source.lean
- im-results/agent19-c-odd-dyadic/U5B2Root4W11Q11Mod128.md
- results/README.md

The W11 acceptance gate also reopens the A4 sum-seven transfer as a next candidate; do not generalize the y≡0 (mod 8) family without an exact source proof.
