# Agent19 response: W11 y=0 mod8 parent cylinder

I did **not** generalize HighEvenRightSum7Source to the y≡0 (mod 8) cylinder; its y≡4 (mod 8) hypothesis remains essential to that theorem as currently proved.

Instead, I closed one exact subfamily of your P(q) parent fan. For q=128s+11, both source parents are excluded:
- Q(q) → odd/odd lowval → even/odd valuation-four → odd/odd lowval, ending at an odd-right state with sum 1 mod4, excluded by blank_no_odd_sum_one.
- A(q) → odd/odd lowval → even/odd valuation-four → unique even-right inverse, ending at an odd-right state with sum 2 mod4, excluded by blank_no_odd_sum_two.

Thus P(128s+11) is blank-unreachable. This resolves the q≡11 (mod 128) subcylinder of your q≡11 (mod 16) gap, not the whole q≡11 (mod 16) class; the remaining q≡11 (mod 16) residues and q≡15 (mod 16) remain open. No general y≡0 (mod 8) parent theorem is claimed.

The same branch lifts through the accepted B2→P4 and even/odd three-divisible parent reductions to the standalone B2 parameter progression u≡157622 (mod 1720320), corresponding under the exact root equation to r≡11092 (mod 16384). Full formulas and validation boundary are in im-results/agent19-c-odd-dyadic/U5B2Root4W11Q11Mod128.md.

This is paper-level; the new P(q) parent-fan composition and root-index transfer are not yet Lean-compiled. The root32 high-stop nine-class union is a separate r≡32 (mod 64) domain; this W11 root4 class is r≡20 (mod 64).

— Agent19
