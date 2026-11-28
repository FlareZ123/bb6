# Reset barrier and eventual affine token-frontier graph

Agent 12, 2026-11-28. **Prepared-state result, not a blank-root halt or a new BB(6) bound.**

## Source-certified reset barrier

In the original #85 token encoding, let CR(K,L) stand for tok_CR K W L, with arbitrary untouched W. For every k, T, c, and Ltail, the aligned word

    CR(k::T, 1 0 0 1 1 0 1 c Ltail)

halts, independently of the stored token tail. The source clauses give CR10, CR0, a high double exposure at head 3, a further CR11 exposure, and a zero-token fatal scan. This does not require the good-stack invariant. The existing good-stack invariant allows synchronization after an arbitrary binary prefix if two zero digits precede the aligned word; a prefix step consumes at most those two delimiters, and otherwise preserves the good-stack property or already halts.

The public theorem a12G_binary_reset_halts in [ResetBarrier.append.lean](ResetBarrier.append.lean) therefore proves halting of every prepared ordinary G state with positive initial zero run and a binary suffix containing 101100100 (reverse of the synchronized token word), with arbitrary binary words on both sides. This is genuinely different from the existing 111 barrier: 101100100 contains no triple. Original-source Lean CI [46093095307](https://github.com/FlareZ123/bb6/actions/runs/46093095307) succeeded at cf7d84504940d51750d41065374270b7e064fd46. The earlier run 46092233879 failed solely because a private token encoding appeared in a public lemma; its repaired lemma is private. The public theorem is checked with the original machine.

The aligned trace costs 96 defined transitions before the undefined halt query. More generally, for z>=1, h=1+2z, q=floor(h/3), h mod 3 equal to 0 or 2, the word

    1 0^(z+1) 110 (10)^(q-1) 1 c Ltail

halts after 12q^2+45q+2z+37 for remainder 0 or 12q^2+45q+2z+55 for remainder 2, independently of k>=1, T, c and Ltail. The high-token exposure decreases the head by 3 and adds four ones per double exposure; successive 10 blocks skip the newly generated ones, leaving a low token before the final double. These timing claims are arithmetic derivations and literal simulation evidence, not yet a separate counted Lean theorem. Tests: z=1..34 (eligible remainders), k in 1,2,3,7,50, T in [],[0],[2,0,1],[1,1,9],[5,2,2], c in 0,1,2,7; 2300 literal comparisons, no discrepancies.

## Exact eventual transducer

Let F(n)=tok_CR [1] [] (replicate n 0 ++ [1]). The [symbolic graph](frontier_symbolic_graph.js) applies the corrected token clauses with affine arithmetic, including the exact subtract-three H batch. A normalized state has one variable positive slot (a value or run length), and all other entries are fixed finite naturals. Each edge is an eventual affine formula n=p*q+r -> n'=a*q+b, with a recorded lower threshold Q and a quadratic exact defined-transition cost. A variable modulo-three test branches p=3, r=0,1,2. A parameter-dependent inequality is resolved only for sufficiently large q; the graph does not silently assert it for small parameters. Zero suffix token padding is physically blank.

For the explored part of the graph every nonterminal edge retained one variable slot and a positive multiplier a coprime to 3, so every finite residue-choice word corresponds to exactly one eventual input cylinder modulo 3^d, where d is its number of variable ternary decisions. This follows inductively by solving a unit congruence and increasing the lower threshold as required. Deterministic edges have zero decision cost; the [counter](frontier_count.js) contracts them until the next ternary split, rejecting loops, unknowns and nonunit multipliers. It propagates BigInt path counts, rather than enumerating exponentially many starting residues. For any fixed depth, finitely many thresholds suffice to cover all sufficiently large input integers. This is an eventual statement; it does not establish the exact behavior of a small input outside those thresholds.

The actual computation to depth 110 had no loops, unknowns or nonunits. The first terminal branch occurs at depth 108, and the exact counts of first-terminal paths were:

| Decision depth | Newly terminal paths | Distinct live split states |
|---:|---:|---:|
| 107 | 0 | 235046 |
| 108 | 1057916215296 | 245366 |
| 109 | 3173748645888 | 256026 |
| 110 | 8463329722368 | 266990 |

The depth 108 count exactly matches Agent32's previously source-certified E/B-route count. This is **not a new count at depth 108**. The independent token graph includes other token branches and provides evidence of minimality within this eventual transducer; it does not prove global minimality of arbitrary halting residue cylinders. Counts at 109 and 110 refer to first terminal decision depth, not cumulative counts at that modulus. The normalized graph is not yet kernel-checked as a complete enumerator. The source-level single-mode CR proof and counted atomic clauses are the intended bridge.

A minimum-decision path found by the graph has 462 elementary macro edges. Its backward lifted input progression is n = 1958886597479621898212194348883469597359005781150465 mod 3^108, with nonnegative free parameter; this is a token-coordinate witness and should not be confused with the ordinary D-family section residue without a verified coordinate bridge. No authentic blank-root reachability follows.

Reproduce with Node.js: node frontier_count.js 110 120000, then repeat with --resume if the time budget expired. The script records every completed layer to a checkpoint file at the end of each invocation; set CHECKPOINT to override the path. A shortest path can be extracted with node frontier_symbolic_graph.js 2000000 108 120000. The scripts use exact BigInt arithmetic for affine coefficients, clocks and path multiplicities; finite RLE constants are checked before conversion to Number.

## Remaining obligation

Agent3 already proves density-one halting for every fixed prepared suffix, and Agent32 already provides a source-certified total ordinary affine recurrence. Do not re-prove these as a new result. The open question is an all-time decision for the actual integer roots, and its connection to current weighted Cover leaves. The new synchronizing word is a target for root-specific arithmetic rather than grounds for a heuristic verdict. The eventual transducer is useful for inverse-target generation but cannot resolve a fixed root merely from residue density.
