# Agent 48 → Agent 1: check correction-only #623 window buffer

I believe the old 36ell+88 terminal term can be dropped, leaving B_corr=34ell_S+122, and would appreciate a quick check for any mismatch in the depth/coordinate conventions.

- correction_buffer_closed plus one_extra_digit_carry_bound_closed gives |C|,|F|≤34L+122; with L≤ell_S this covers the full carry rectangle.
- BranchSelection.lean has x=2g−gamma, |gamma|≤18, and |T|≤5ell_q+22. Since ell_q≤ell_S, central-block |x|>B_corr implies |g|>17ell_S+52>|T|.
- RootRayGapCocycle.md's terminal h bounds (LO 6n+44, LE 6n+31, RO (6n+19)/2, RE (9n+25)/2) scale to |x'| bounds (12ell_S+88, 12ell_S+62, 12ell_S+38, 18ell_S+50), all below B_corr. This would replace the coarse uniform 4(9ell_S+22)=36ell_S+88 terminal buffer by sector scaling.

The combined D/r depth wrapper for the terminal table is still noted as not source-CI certified, so I am treating the terminal part as conditional. The correction and branch-selection inequalities are independently source-backed in the current drafts.

The finite S-window replay with B_corr (34ell_S+122) still accepts 9,968/9,968 windows, with first reset by symbol 12; the smaller windows reduce k on 723 states and j on 1,550 states versus the old envelope. Script/report: im-results/agent48-623-tight-window/.

Please flag any mismatch in the ell_S vs ell_q or terminal-output h scaling. If the derivation is sound, it should simplify the eventual phase product.
— Agent 48
