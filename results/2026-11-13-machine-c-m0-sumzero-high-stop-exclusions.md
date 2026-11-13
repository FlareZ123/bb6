# Machine C: source-certified m=0 even-even sum-zero high-stop exclusions

## Theorem

Let CReach(x,y) be eventual reachability from the authentic blank-derived section seed (5,1), using the original Machine C section transition. For an m=0 high-stop pair satisfying

k+j+5 = 4(j+3),

the following four disjoint infinite parameter families are unreachable:

| j | forced k |
| --- | --- |
| 1895+2048v | 5692+6144v |
| 359+8192w | 1084+24576w |
| 5479+16384w | 16444+49152w |
| 10599+32768w | 31804+98304w |

In every row, the parameter ranges over all nonnegative integers and not CReach(2j+3,k).

The four families correspond to the odd parameter t=(j-7)/32 in the disjoint cylinders t≡59 (mod 64), t≡11 (mod 256), t≡171 (mod 512), and t≡331 (mod 1024). Their union has exact natural density 23/512 within the odd-t parameter ray. This is not a fraction of machines, halts, or BB(6) cases decided.

## Proof architecture

The exact high-stop predecessor equations first reduce each root target (2j+3,k) to (17+64t,28+96t). The source theorem mzero_first_two_reach then reduces that configuration to A_s=(130+208s,94+152s), where t=2s+1 and j=7+32t. For odd s, source parent extraction proves that reachability of A_s forces reachability of L_s=(222+360s,46+76s) or B_s=(54+90s,127+211s).

For even-even targets (x,y) with x>0, y≥6, x,y even, x+y=8S, S>2, and S%4≠0, the source theorem even_even_sumzero_parent proves that every source parent is either the direct parent (x+y-2,(y-2)/2) or the depth-one even-a bounce parent (2S-2,(x+2y-2S-8)/2). The proof derives this from the complete original-source section_preimage_all_iff grammar. It excludes the zero-left branch by the non-power-of-two condition, the one-left and odd-left branches by parity, and deeper even-left bounce branches because they force 4|S.

The odd-image invariant excludes odd-right states with coordinate sum 1 modulo four. The exact six-of-eight inverse equivalence reduces even-right states with y≥6 and nonzero/non-seven sum residue modulo eight.

For s≡5 (mod 8), L_s is excluded uniformly. For s=256w+85, three six-of-eight inverses reduce B_s to an even-even sum-zero target with S=5195+15540w and S%4=3; both source parents are odd-image forbidden. For s=512w+165, seven six-of-eight inverses reduce B_s directly to an odd-right state with coordinate sum 1 modulo four. The earlier s=32v+29 and s=128w+5 families are proved by their exact source-parent and six-of-eight chains in the same module.

## Formal verification

The standalone Lean source is ../im-results/agent11-c-low58/M0EvenEvenSumZero.lean, namespace BB6.Agent11M0SumZeroVerified. Original-source Lean 4.36.0-rc2 CI 43383761248 compiled the full module, including all four high-stop theorems and their axiom audits. Every printed theorem has axiom profile [propext, Classical.choice, Quot.sound], with no sorryAx.

The manual-only Agent 11 milestone workflow now includes this standalone module for future reproducible checks.

## Scope and open cases

The generic even-even parent theorem deliberately assumes S%4≠0. The S%4=0 parent tree, the odd-s residual outside these four cylinders, and especially s≡7 (mod 8), remain open. The split files M0EvenEvenSumZeroParents.lean, M0EvenEvenSumZeroRays.lean, and CThreeDiagonalM0SumZeroFull.lean are separate unverified drafts and are not certified by the standalone proof run.

These exclusions do not decide Machine C, establish a global six-state upper bound, or determine the exact value of BB(6).