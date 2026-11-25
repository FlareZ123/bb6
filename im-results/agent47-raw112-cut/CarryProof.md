# Raw112 F1=0LE: recursive carry proof

Literal partial table: `1RB0RF_1RC0LB_0RD0LB_1LD1RE_0RA1LC_---0LE`. Missing F0.

**Status:** all-depth proof locally compiled with Lean 4.36.0-rc2 against a literal copied zipper-semantics fixture (no assumed lemmas). Original-source import integration via Raw112CarryNever is pending. This is not a bounded simulation. The other raw112 residual is separate.

## Proof
The blank run reaches C after 382 steps, with scanned 0, nearest-first left word 1, and right word (excluding scanned cell) 00 (110000)^n 001111 L(n mod 6) H(floor(n/3)), n=1. L and H are defined in the proof files. The invariant is proved for every n >= 1, following Agent19's observed base-six encoding.

- Raw112CarrySweeps: arbitrary-context local sweeps, pumped by induction. Three outer sweep sections cost 88j+165, 50j+85, 12j+26, with j=n-1.
- Raw112HighIncrement: H(k) has six seeds; for k=6m+r, m>=1, a parity-dependent 15-bit digit prefix is followed by H(m). The state E increment is proved by strong induction on k, returning to D on even k and B on odd k. Ordinary digit transitions preserve arbitrary left/right contexts. Carry r=5 recurses on m with the frame preserved; even m costs 77+t+23 and odd m costs 75+t+15. The base carry k=5 costs 121.
- Raw112CarryRoot: six low phases compose both suffix operations with the outer sweep theorem, proving positive-cost growth from family j to family (j+1). Blank entry and unbounded_live are proved, giving arbitrarily long successful primitive prefixes, with no F0 lookup.
- Raw112CarryNever: adapter to original NeverHalts API, pending original-source compilation.

The local Lean axiom reports for high_inc, growth, entry, and unbounded_live contain only standard Lean axioms (propext, Classical.choice, Quot.sound). Once the original-source adapter compiles, this excludes every completion of the missing F0 slot. It does not itself close the second residual or the entire raw112 parent.
