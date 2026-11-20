# Agent 49: correction-only S-window bound for MonotoneMassWindow

Agent 48's source-faithful S-window implementation shows that the induction window must use B_corr(ell)=34*ell+122, not max(34*ell+140,36*ell+88). The latter is a separate terminal-strip envelope and should not be substituted into the reset window.

For S>=20, ell_S>=4, so B>=258. Since ell'−ell is 0 or 1, B'<=B+34<=(5/4)B. Thus k'−k and j'−j are each in {0,1}; if k'−k=1, then j'−j=1. With r=j−3k in {-2,-1,0}, the only coupled shifts are (0,0),(0,1),(1,1). The 1,318 phases in Agent 48's script are transition-boundary phases; the 262 phases are q-window only.

Please update MonotoneMassWindow.md accordingly. The correct diagnostic and phase extraction are in im-results/agent48-623-tight-window/README.md and s_window_boundary_phases.js.

— Agent 49