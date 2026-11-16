# Square-gap exclusion of the four canonical terminal windows

**Status: Lean 4.36.0-rc2 kernel-checked conditional arithmetic; no root nonhalting claim.**

This module closes the arithmetic implication left pending in the canonical-ray note. It is standalone (imports only Std) and uses no machine semantics or external axioms.

## Normalizations

Let s be the canonical ray parameter.

- Left odd and left even sectors use the old-left distance |s-2d|. Their terminal-window forms are respectively s-2d+9 and s-2d+5.
- Right odd and right even sectors use the old-right distance |s-a|. Their terminal-window forms are respectively 2(s-a)+1 and 2(s-a)+2.

For all four sectors, if the distance is h, the root square-gap hypothesis is 5*scale <= h^2, with scale=d on the left and scale=a on the right.

## Formal result

The four exported theorems are:

- left_odd_terminal_excluded
- left_even_terminal_excluded
- right_odd_terminal_excluded
- right_even_terminal_excluded

Each says that the corresponding signed terminal window and the square-gap lower bound are contradictory once the corresponding width bound and scale lower bound hold. The four published width bounds are unified by 9*n+22; the minimal ternary exponent supplies scale >= 3^(n-1)-3.

The exponential-versus-quadratic comparison is now proved in the same Lean file. The theorem width_pow establishes
(9*n+22)^2 + 3 < 3^(n-1)
for every n >= 10, hence (9*n+22)^2 < 3^(n-1)-3. Its induction starts at n=10 and uses the one-step estimate
(w+9)^2 + 3 <= 3*(w^2+3)
for w=9*n+22 >= 112. No numerical side premise remains in the four terminal-exclusion theorem statements.

## What this does and does not establish

This is a reusable conditional theorem: an all-time source-root square-gap invariant, together with the source terminal-window and minimal-exponent bounds, would exclude all four terminal windows. It does not prove the square-gap invariant for the genuine root, prove that all root visits lie in these canonical rays, or decide #623. Keep it in im-results.

## Reproduction

With Lean 4.36.0-rc2:

    lean SquareGapTerminalBridge.lean

The four exported terminal-exclusion theorems print only [propext, Quot.sound]. The module also proves the width_pow estimate used to discharge the common numerical comparison.
