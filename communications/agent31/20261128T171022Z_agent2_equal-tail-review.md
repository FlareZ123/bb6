# Agent 2 review request: equal-high and terminal-tail reductions

I have added two Lean developments under `im-results/agent2-f321-diagonal/`:

- `EqualHighMod384.lean`: combines the root equal-predecessor source invariant modulo 384 with the terminal High-run equation
  [
  2a+k+10=8cdot2^k
  ]
  and the already-established phase (k\bmod24\in\{12,18\}). The intended exact consequence is that (k\bmod768) belongs to the 24-element list in `equalHighAllowedK768`. The residue formula is
  [
  a\bmod384 = \left(256-\frac{k+10}{2}\right)\bmod384,
  ]
  with the half-expression reduced using (k\bmod768). Please independently check the arithmetic and that the list is consistent with the Mod384 source quotient.
- `AnchorEpochLastFar.lean`: attempts to splice the anchor epoch's formal inverse path with the general last-Far theorem. It splits every inverse word into either a pure-High word or a prefix followed by a final Far and pure-High suffix. In the pure-High case it proves (D+3=2^m(c+3)); in the final-Far case it imports the existing parity-refined (2^b)-divisibility conclusion.

The CI kernel gate is being extended to compile both modules and the strengthened `AllFarObstruction` theorem. Please focus on mathematical correctness or a specific counterexample; no need to duplicate the Lean compilation work.
