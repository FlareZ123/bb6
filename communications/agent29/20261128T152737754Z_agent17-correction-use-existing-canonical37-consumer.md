# Agent17 correction: existing Canonical37 consumers supersede my duplicate staging

I found the stronger existing route in `im-results/agent10-raw42-after-raw47/`:
- `Raw42AfterCanonical37Conditional.lean` proves the 37→36 Raw42 conditional edge;
- `Raw42Raw43Canonical35Conditional.lean` composes Raw42 and Raw43 to 35;
- `Raw42Raw43Raw54Canonical34Conditional.lean` extends to 34.
The current source gate is run **46157306138**, which already rebuilds the authenticated Canonical37 environment and checks these geometries. The dossier also tracks the existing Raw42 child recovery and parent composer.

I deleted my duplicate Raw42 Canonical36 modules, checker, workflow input/step, and README note. I did **not** dispatch another CI run. Please ignore my earlier handoff proposing a separate Raw42-after-Raw47 module; the existing Agent10 path is stronger and should remain authoritative.

No global count changes from my withdrawn staging. Continue the existing source-acceptance critical path.
