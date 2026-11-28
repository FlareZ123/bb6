# D100 E0-hole unary doubling: exact inductive nonhalting certificate

Literal `1RB1LA_1RC1LE_0RD0LB_0LD0LA_---0LF_1LC0RA`. This was one of the three persistent D100 one-hole literals after the long-epoch B1 pump. **New mathematical result:** its blank run enters an exact doubling family. The proof is checked locally in Lean 4.36.0-rc2 against the verbatim Z0 transition, rep, join0, sweepL and sweepR core from SweepPumping; the complete original-source bridge and axiom acceptance remain to be performed. Source module: [D100UnaryDouble.lean](D100UnaryDouble.lean). No global Cover count changes yet.

## Exact macro

Use the original nearest-first zipper; the scanned square is the head of the left list or zero when empty. Write U=11, V=1010, W=1111. Define A(m,z) = (A, [], 1 U^(m+2) 00 0^z) and C(j,m,z) = (C, [], V^(j+1) 1 U^m 00 0^z). All parameters are natural. The exact 199-step blank prefix reaches A(3,5), i.e. eleven ones and seven explicitly represented zeros to the right of the blank head. The following identities hold with all untouched tails quantified:

* A(m,z) -> C(1,m,z) in 50 steps.
* C(j,m+1,z) -> C(j+1,m,z) in 16(j+1)+8 steps.
* C(j,0,z) -> A(2j,z+1) in 12(j+1)+9 steps.

For the middle law, the 8-step right transfer replaces each V by W; it starts with an empty left list, then retains a zero frame. Four steps at the boundary consume two ones and leave a three-one frame. An 8-step left transfer repeatedly replaces W by V, and four final steps remove the frame and prepend another V. The terminal law uses the same right transfer, an 8-step turn at the final 100, one left move and a 4-step A sweep for each W. These are finite `rfl` identities with arbitrary unexamined tails, iterated using the already source-proved general sweep lemmas.

Induct on m: A(m,z) returns to A(2m+2,z+1) after exactly 8m²+44m+83 steps (the Lean module uses the equivalent recursive sum to avoid nonlinear arithmetic). The unary length n=2m+5 thus evolves by n'=2n-1. At m=3 the first cost is 287, then 947 at m=8; these agree with the independent primitive trace. Every epoch has positive cost and uses defined, nonhalting transitions. Hence every total completion of the E0 hole never halts, by the original `never_of_growth` bridge.

## Evidence boundary

Local Lean checks of `entry` and `growth` passed with only [propext] and [propext, Quot.sound] respectively, using a reconstructed exact-core model rather than a checkout of the full source (the local shell cannot resolve github.com). The committed source imports the real SweepPumping module and exports `BB6.Agent7D100UnaryDouble.never`. It requires a complete original-source acceptance run, including that theorem's axiom profile, before it is counted as a formally accepted D100 leaf. No new workflow is needed; use the existing manual shared Lean source closure. There is no claim that all D100 leaves or BB(6) are resolved.
