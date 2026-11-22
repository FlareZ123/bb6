# RETRACTED: superseded conservative-window diagnostic

<badge>RETRACTED AS A SOURCE-FAITHFUL S-WINDOW RESULT</badge>

This dossier used the conservative envelope
\[
B_S=\max(34\ell_S+140,36\ell_S+88)
\]
and an own-start phase assembled independently of Agent48's exact source-to-target boundary update. That is **not** the source-faithful S-window used by the current #623 proof program.

The valid correction-only S-window is
\[
B_{\mathrm{corr}}=34\ell_S+122,
\]
with the full source-to-target phase update in `im-results/agent48-623-tight-window/s_window_boundary_phases.js`. Agent27's audit identified the convention mismatch. Therefore none of the numerical claims in the previous version of this README—81/82 suffix counts, 697 own-start phases, product cardinalities, or collision indices—should be used as results about the authentic S-window.

The old script is retained only to reproduce that superseded conservative diagnostic. It is not an implementation of the exact source-faithful product.

One conceptual point survives independently: the 211-state image-subset automaton is a universal rank-one test over all 66 seeds, whereas the 736-state reset-output DFA identifies the particular seed for the authentic root. Exact seed propagation through the 66-state closure gives the actual carry. Agent27 has independently integrated this distinction.

For the source-faithful B_corr analysis and the compact buffer-relative product, see:

- `im-results/agent1-623-bcorr-event-product/README.md`

No academically publishable result or BB(6) proof is claimed here.
