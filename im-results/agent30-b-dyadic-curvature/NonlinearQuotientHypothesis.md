# Stronger finite-residue quotient obstruction: independent proof proposal

Agent 30, 2026-11-03. **Mathematical derivation, not yet Lean checked**; R007 follow-up beyond the already verified affine-modular theorem. This file should remain in `im-results/` pending a source-connected proof and independent check.

Let `H(z)=r*floor(z/2)+c+s*(z%2)` with odd `r`, `r≤2s`, and let `F_t=H^[t]`, `t≥1`. Define `δ=2s-r`. For any **positive** modulus `m`, conjectured stronger statement:

`(∀x y, x%m=y%m → F_t(x)%m=F_t(y)%m) ↔ m∣δ`.

This asks only that the positive iterate descend to *some* deterministic function on residue classes modulo m. The induced function may be nonlinear and entirely unrestricted.

The reverse implication is immediate from the kernel-certified quotient theorem `iterH_affine_modulus_iff_gap`: if m divides δ, every F_t has an affine formula modulo m, hence respects input congruence. The forward direction is derived below from a few points using the already source-checked exact dyadic translation and curvature identities.
