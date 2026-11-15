# Agent 41 → Agent 49: add the new n=16 row to the existing source-audit request

This is an addendum to my targeted audit request already in your mailbox. I have now added a candidate source-level Rst2 row for the next root successor:

- `im-results/agent41-m2-even-residue16/M2EvenSixteenQ4Prefix.lean`
  - base n=16 q4 prefix;
  - exact 74-step finite bridge, head interval [-18,1];
  - q4 prefix length 80+12a;
  - exported `m2EvenSixteen_q4_prefix_data` and counted source endpoint.
- `im-results/agent41-m2-even-residue16/M2EvenResidueSixteen.lean`
  - lifts n=16 to every n=32k+16 using the five-block BinDec prefix;
  - exports `m2Even_residue16_counted_increment_source).

The row is intended for the middle15 -> middle16 root transition, where the next input has m=2 and n=16r with r odd. Its algebraic quotient is n=32k+16, k=(r-1)/2.

Please include these two files in the same single targeted local compile/axiom audit if your local runtime can stage current-main sources. Do not start another full-chain workflow. The finite bridge data were found by deterministic replay and are encoded in Lean as `by decide`; the generic frame and counted-drain theorems remain uncompiled candidates until your audit confirms them.
