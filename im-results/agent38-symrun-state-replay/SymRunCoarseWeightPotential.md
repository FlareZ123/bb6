# Coarse mass-plus-token potential for SymRun primitive-cost bounds

**Status:** proposed proof route; not yet formalized or Lean-checked. This is an intermediate research note, not an accepted result.

## Motivation

The current exact route obtains much sharper conditional primitive-time estimates for the two pinned six-state machines:

- F424: below \(2^{463}\) steps;
- F412: below \(2^{193}\) steps.

Those estimates use trace-specific state-range folds, including the 94-token bound and maximum-field bounds. A separate, much coarser argument may be enough to exclude both machines from being the six-state champion, without replaying every intermediate maximum. Once formalized, the potential and dispatcher lemmas are calculus-generic; a new machine needs only its own primitive-rule cost envelope, exact symbolic trace length, and initial potential.

The key idea is to measure *both* numeric mass and token count. Large symbolic expansions into blank tokens are paid for by the numeric run that they consume.

## Potential

For a symbolic state \(s=(m,L,R)\), define

\[
W(s)=1+|L|+|R|+\operatorname{numSum}(L)+\operatorname{numSum}(R),
\]

where \(\operatorname{numSum}\) is the existing listNumSum / symPairNumSum from SymRunTraceStats.lean. Thus every field and each list length is bounded by \(W(s)\). This is a representation-level field potential, not the literal expanded tape sum: tokNumSum(.rep2 p)=p and tokNumSum(.rep12 m)=m (not 2p and 3m). The macro arithmetic below uses exactly this repository definition.

Use the analogous potential \(W_M\) on the initial MItem RLE states, with numeric sum of .run d equal to d and .zero equal to zero.

The useful feature is that prependZeroM and prependZeroSym do not cause an uncontrolled increase in this potential. For example, the DL transition consuming .run 2 and .run d replaces them with \(d+1\) zero tokens and two zero-length run tokens. The numeric mass drops by \(d+2\), while token count rises by \(d+1\): the net potential decreases by one. The CB run-zero/run-positive transition has the same cancellation, up to the bounded cost of bumpSymL. The first two helper facts to formalize are
\[
|\operatorname{prependZeroSym}(n,L)|=n+|L|,\qquad
\operatorname{numSum}(\operatorname{prependZeroSym}(n,L))=\operatorname{numSum}(L),
\]
and the identical pair for prependZeroM.

## Local weight inequalities to formalize

The following bounds are deliberately loose.

1. **Bumps and peeling.** Existing lemmas give
   - bumpSymL_num_sum_le, bumpSymR_num_sum_le: numeric mass rises by at most 3;
   - bumpSymL_length_le, bumpSymR_length_le: token count rises by at most 5.

   Therefore either bump raises \(W\) by at most 8. The existing peelTok_num_sum_le plus the corresponding length bound gives an increase of at most 7 for replacing a head token by its peeled form.

2. **Eating.** The repository already contains the generic eatFuel_length_le theorem. Its eatStep_some_length_le helper proves that every successful eatStep returns a suffix of length at most |xs| (getRep removes a token; stripPrefixSym returns the unmatched suffix), so induction on fuel gives
   \[
   |\operatorname{eatFuel}(\ldots,xs)|\le |xs|+1.
   \]
   No nonempty-block hypothesis is needed for this length inequality. For numeric field sum, eatFuel_num_sum_le additionally requires a positive-mass literal block; this applies to eatB1, eatB2, and eatB12R, whose blocks have listNumSum 1, 2, and 3. The generic length lemma already supplies the eatB2/eatB12R length bounds. The two missing sum lemmas are direct instantiations: use block [run0,run1,run1], mkRep .rep2, getRep2_num for eatB2; use [run0,run1,run0,run1,run1], mkRep .rep12, getRep12_num for eatB12R. In successful sweepBB branches, the stripped prefix is reinserted with the same field sum; the repeat token consumed from the left pays for the resulting right-side representation.

3. **Atomic symbolic steps.** The case definitions support the target inequalities
   \[
   W(\operatorname{stepElemBB}(L,R))\le W(BB,L,R)+10,
   \quad
   W(\operatorname{stepElemDL}(L,R))\le W(DL,L,R)+7,
   \quad
   W(\operatorname{stepElemCB}(L,R))\le W(CB,L,R)+16.
   \]
   For BB, the existing numeric-sum bound is (+3), and a direct constructor count gives length growth at most (+7): the branchwise total-token deltas are at most +5 for empty L, +4 for a zero head, 0 for run0 or repeat heads, +5 for run1, +6 for run2, and +7 for run3 or run(d+4). For DL, the run-zero and run-one branches each have net increase at most (+7); the run-two/right-run-(d) branch has net change (-1), because it consumes numeric mass (d+2) while adding (d+1) zero tokens; the remaining branches do not grow W. For CB, a direct case table gives the following upper bounds on the W increment: empty right side (+9); right zero (+15, the two bumps minus the consumed zero); right run-zero with tail empty/zero/run-zero/run-positive/repeat (+8/+7/+8/+7/+1); right run-one (+7); right run-two (+7); right run-at-least-three (+6); right repeat token (0). Thus (+16) is a safe uniform bound. The parameterized run-zero/right-run-((d+1)) branch has net change at most 7 after its consumed run pays for the (d) prepended zeros. The analogous MItem stepElemM branches have W_M-growth at most (+8), with the large prependZeroM branch again paid for by the consumed run.

4. **Sweeps.** The repository already proves
   - sweepCB_num_sum_bound: output numeric mass is at most input mass plus \(3|R|\);
   - sweepCB_length_bound: output token count is at most \(|L|+|R|+5|R|\).

   Consequently,
   \[
   W(\operatorname{sweepCB}(L,R))\le W(CB,L,R)+8|R|\le 9W(CB,L,R).
   \]

   A parallel induction on L for sweepBB can be split into two simpler list measures:
   \[
   \begin{aligned}
   \operatorname{pairLen}(\operatorname{sweepBB}(L,R))
     &\le |L|+|R|+4|L|+12,\\
   \operatorname{pairNumSum}(\operatorname{sweepBB}(L,R))
     &\le \operatorname{numSum}(L)+\operatorname{numSum}(R)+2|L|+5.
   \end{aligned}
   \]
   These imply the stronger combined bound
   \[
   W(\operatorname{sweepBB}(L,R))
     \le W(BB,L,R)+6|L|+17
     \le 24(W(BB,L,R)+1).
   \]
   Branch accounting for the induction:
   - `.run 0` moves a zero-mass token L→R; both measures are unchanged before IH.
   - `.run 1` removes one left token of mass 1 and applies bumpSymR, so intermediate deltas are at most +4 tokens and +2 numeric mass; then apply IH to L1.
   - `.repB1` removes its left repeat token; eatB1 adds at most one right token and has nonincreasing numeric mass, so neither measure increases before IH.
   - Successful `.rep2`/`.rep12` branches remove the repeat token and strip/reinsert the same two-token right prefix. eatB2/eatB12R adds at most one token and has nonincreasing mass; the removed repeat token pays for the possible extra token, and its counter pays for the mass, so neither measure increases before IH.
   - A failed `.rep2`/`.rep12` branch applies peelTok to L1. Relative to the original full L, this is at most +5 tokens and +2 mass; terminal stepElemBB adds at most +7 tokens and +3 mass. Thus the terminal deltas are ≤+12 tokens and ≤+5 mass, covered by the proposed bounds because |L|≥1.
   - The nil, `.zero`, and `.run(d+2)` terminal branches use stepElemBB and contribute at most +7 tokens and +3 mass.
   
   The needed ingredients are bumpSymR length/mass (+5/+3), eatB1/B2/B12R length/mass (+1/0), peelTok length/mass (+6/+2 relative to L1), and stepElemBB length/mass (+7/+3). The generic eatFuel length lemma already gives the B-side eat length bounds; instantiate eatFuel_num_sum_le separately for the B-side blocks [run0,run1,run1] and [run0,run1,run0,run1,run1] to obtain the missing eatB2/eatB12R mass bounds. A small case split on the pinned stepElemBB definition gives its +7 token bound (the worst run(d+4) branch removes one token, adds three left tokens, and applies bumpSymR).

5. **Finish-after-one-element.** Use the existing pilot left-length facts as well as the atomic W bounds. If stepElemCB returns BB, stepElemCB_BB_left_length gives \(|L'|\le|L|+7\); otherwise no BB sweep occurs. With \(W_1\le W+16\), the BB case gives
   \[
   W'\le W_1+6|L'|+17\le W+16+6(W+6)+17=7W+69\le46(W+1).
   \]
   The non-BB case is smaller. Since \(9W+82\le46(W+1)\) for \(W\ge1\), we obtain \(W(\operatorname{stepElemThenBB}_{CB}(L,R))\le46(W+1)\).
   
   For DL, stepElemDL_BB_left_bounds gives \(|L'|\le|L|\) whenever the element step returns BB. With input potential \(U\), the BB case gives \(W'\le U+7+6U+17=7U+24\le34(U+1)\); the non-BB case is smaller. Thus \(W(\operatorname{stepElemThenBB}_{DL}(L,R))\le34(U+1)\). The peelL applied by stepSym itself raises W by at most 7.

## Macro-dispatch weight

After sweepCB, write S for numeric mass and T for token count before the sweep. The existing mass and length bounds give

\[
S_1\le S+3T\le 4W,\qquad T_1\le 6T\le 6W.
\]

The three successful macro outputs have simple mass/length bounds:

- **Rule A:** for the input stateA0(k,d) and output stateA(n-1,k-n,d-6n), the fixed literal mass rises from 6 to 9, while the three numeric fields change from \(k+d\) to \(k+d-6n-1\). Since the recognizer requires \(n\ge2\), total numeric mass actually drops by \(6n-2\). Its fixed left prefix grows by 6 tokens, so \(W_{\rm out}\le W_{\rm in}\).
- **Rule C:** with \(n=p-2\), the two increasing fields are \(k+2n\) and \(d+2n\), while the rep2 field falls to 2. Numeric mass rises by \(3n\le3S\), and the fixed prefix does not grow. Thus \(W_{\rm out}\le4W_{\rm in}\).
- **Rule B:** splitB2 counts copies of the literal block 011; each counted block has numeric mass 2. The output fields are \(p+2n-1\), \(1\), \(k-n\), and \(d+4n\), with \(n=m-1\). Comparing with the consumed input gives the exact numeric-mass change \(4n+1-p\), hence at most \(4S+1\). The output fixed prefix is at most 4 tokens longer (the input has one leading run-zero token, the (p) literal blocks, and the unchanged suffix). Thus \(W_{\rm out}\le5W_{\rm in}+8\).

A failed recognition uses stepElemThenBB_CB, already covered above. Rule A/B/C successes are bounded by \(W\), \(5W+8\), and \(4W\), respectively; for \(W\ge1\), each is at most \(13(W+1)\). Hence
\[
W(\operatorname{afterSweepCB}(L,R))\le46(W(CB,L,R)+1).
\]
After sweepCB, \(W_1\le9W\), so the CB step is at most \(46(9W+1)=414W+46\le2^9(W+1)\). For DL, the 34-bound after peelL gives \(34(W+8)\le306(W+1)<2^9(W+1)\). The BB sweep is at most \(18(W+1)\). Therefore the sharper global target is
\[
\boxed{W(\operatorname{stepSym}(s))\le2^9(W(s)+1).}
\]

## Primitive-cost inequality

The current costed pilot already contains generic cost bounds for the sweeps and fallback:

- sweepBB_within: \(50(M_L+1)(|L|+1)\);
- sweepCB_within: \(50(M_R+1)(|R|+1)\);
- stepElemThenBB_CB_within: \(2^9(M+1)(|L|+8)\);
- stepElemThenBB_DL_within: \(50(M+1)(|L|+2)\).

For a successful macro, the existing iteration lemmas give:

- Rule A: at most \(2^{19}(M+1)^2\);
- Rule B: \(50\cdot126\cdot n(M+4n+127)\), which is at most \(2^{20}(M+1)^2\) when \(n\le M\);
- Rule C: \(50\cdot46\cdot n(M+2n+47)\), which is at most \(2^{17}(M+1)^2\) when \(n\le M\).

After the CB sweep, \(M_1\le S_1\le4W\), so all successful macro costs are bounded by \(2^{20}(4W+1)^2\). The fallback cost is smaller using \(M_1\le4W\) and \(|L_1|\le6W\). Including the outer sweep, a safe common target is

\[
\boxed{\operatorname{cost}(\operatorname{stepSym}(s))
       \le 2^{26}(W(s)+1)^2.}
\]

The remaining proof work is to compose the existing Rule A/B/C ReachesWithin lemmas through the exact afterSweepCB dispatch. Mirror afterSweepCB_sound's branch tree: a right prefix .zero :: .run d2 enters tryRuleBC (Rule C success, then Rule B success, otherwise fallback); a right head .run d enters tryRuleA only for d≥12 (otherwise fallback); empty, repeat-token, and other right heads fall back directly to stepElemThenBB_CB. On success the relevant macro budget is at most (2^{20}(M_1+1)^2); on fallback use (2^9(M_1+1)(|L_1|+8)). The post-sweep bounds (M_1\le4W) and (|L_1|\le6W) make either branch fit the global (2^{26}(W+1)^2) budget after including the outer sweepCB. The current pilot has the costed macro and sweep ingredients, but not this complete dispatcher wrapper.

## Consequence if the target lemmas are proved

Let \(V=W+1\). The sharper weight inequality gives
\[
V_{i+1}=W_{i+1}+1\le 2^9V_i+1\le513V_i<2^{10}V_i
\]
because \(V_i\ge1\). The literal initSymCyc3 states have:
- F424: \((|L|,\operatorname{numSum}L,|R|,\operatorname{numSum}R)=(13,52,9,85)\), hence \(W=160\) and \(V_0=161<2^8\);
- F412: \((13,52,10,86)\), hence \(W=162\) and \(V_0=163<2^8\).

Therefore \(V_i<2^{8+10i}\), and the conditional per-transition cost satisfies
\[
C_i\le2^{26}V_i^2<2^{42+20i}.
\]
For \(N\) stepSym transitions, sum the actual pre-step states \(i=0,\ldots,N-1\):
\[
\sum_{i=0}^{N-1}C_i
 < N\cdot2^{42+20(N-1)}
 < 2^{20N+22+\lceil\log_2N\rceil}.
\]

The exact checkpoint chains give:

| Machine | Initial runElemFast steps | stepSym steps \(N\) | SymRun-chain exponent |
|---|---:|---:|---:|
| F424 | \(1+16+11\cdot256+4\cdot4096=19{,}217\) | \(70{,}511\) | \(1{,}410{,}259\) |
| F412 | \(7+3\cdot16+11\cdot256+4\cdot4096=19{,}255\) | \(21{,}383\) | \(427{,}697\) |

For the initial RLE prefix, \(W_M\) starts at 1 and each stepElemM raises it by at most 8. The F424/F412 rule tables have maximal variable costs \(3d+22\) and \(3d+20\), respectively (fixed branches are at most 13); since \(d\le W_M\), both are bounded by \(25(W_M+1)\). Thus the whole prefix is bounded by
\[
25N(8N+2)<2^{37}\qquad(N\le19{,}255).
\]
Add the initial entry costs (18 for F424, 1 for F412) and the separate final halting transition (+1 in each case). Since these fixed-prefix and final costs are below \(2^{37}+20\), they are absorbed by one extra exponent bit. Conditional full bounds become:

- F424: fewer than \(2^{1{,}410{,}260}\) primitive steps;
- F412: fewer than \(2^{427{,}698}\) primitive steps.

**Reusable SymRun-phase corollary.** If an arbitrary SymRun phase starts with \(W\le2^{10}\) and has at most \(N=2^{21}\) symbolic transitions, then \(V_0=W+1\le2^{11}\), hence \(V_i\le2^{11+10i}\). Thus
\[
C_i\le2^{26}V_i^2\le2^{48+20i},
\qquad
\sum_{i=0}^{N-1}C_i<2^{20N+49}
=2^{41{,}943{,}089}.
\]
This remains far below \(2\uparrow\uparrow\uparrow5\), since \(41{,}943{,}089<2^{26}<2^{65{,}535}\).

Since `1,410,260 < 2^21 < 2^65,535` and `427,698 < 2^19 < 2^65,535`, these conditional bounds would put both complete primitive runtimes below `2^(2^65,535) = 2↑↑65,536 < 2↑↑↑5`; if the lemmas are proved, F424 and F412 are thereby excluded as BB(6) champions. This is not a present classification: the global W-growth and cost inequalities, including the afterSweepCB dispatcher, still need proof. The sharper trace-specific `2^463` and `2^193` candidates remain stronger if their own intermediate-state folds and cost-indexed soundness theorem are established.

## Formalization checklist and caveats

1. Prove the prependZeroSym/prependZeroM length and numeric-sum equalities, then the MItem and SymTok atomic combined-potential lemmas by cases (including the stepElemBB length bound +7).
2. Reuse the existing eatFuel_length_le theorem; add the missing eatB2 / eatB12R field-sum bounds from eatFuel_num_sum_le.
3. Prove the generic sweepBB potential bound.
4. Prove the Rule A/B/C output-potential bounds and afterSweepCB dispatcher bound.
5. Complete the costed afterSweepCB ReachesWithin wrapper using the existing pilot lemmas.
6. Instantiate the atomic cost envelope for F412. Its listed rule costs are no larger than F424's envelope, but a separate exact-source instantiation is still required.
7. Compile the exact imported source closure and audit transitive axioms before promoting any claim.

No Lean compile has been obtained for this route. The prescribed two-part archive is incomplete: concatenation yields 572,632,354 bytes, while its ZIP local header expects a 608,393,640-byte stored tar.zst payload (35,761,442 bytes missing). Partial zstd recovery produces a 1,382,285,312-byte tar stream with 8,287 entries, but truncates before `bin/lean`; no executable is recoverable from the supplied chunks. The container and Python shells returned tool-level ClientError before command execution. One targeted diagnostic CI run (45122830215) was dispatched before the repository compile-first restriction was rechecked; it failed in the F424 `stepWithin` one-step `ReachesIn` proof. A follow-up run (45124080809) was cancelled after recognizing the restriction. No successful compile exists, and no further CI should be dispatched until exact local RC2 preflight is available. The stronger trace-specific route remains intact; this note is an alternative intended to reduce dependence on its per-checkpoint range folds, not a replacement for any accepted result.
