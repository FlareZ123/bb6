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

2. **Eating.** For the concrete nonempty blocks used by eatB1/eatB2/eatB12R, eatFuel_num_sum_le proves that a positive-mass block is exchanged for its repeat counter without increasing numeric mass. The length lemma
   \[
   |\operatorname{eatFuel}(\ldots,xs)|\le |xs|+1
   \]
   follows by induction on fuel, with the nonempty-block hypothesis: every successful eatStep returns a strict suffix (getRep removes one token; stripPrefixSym removes a nonempty block). On no match, eatFuel emits one repeat token before xs; on a match, the induction hypothesis bounds the result by the shorter suffix length plus one, hence by |xs|. In successful sweepBB branches, the stripped prefix is reinserted with the same mass; the repeat token consumed from the left pays for the resulting right-side representation.

3. **Atomic symbolic steps.** The case definitions support the target inequalities
   \[
   W(\operatorname{stepElemBB}(L,R))\le W(BB,L,R)+10,
   \quad
   W(\operatorname{stepElemDL}(L,R))\le W(DL,L,R)+7,
   \quad
   W(\operatorname{stepElemCB}(L,R))\le W(CB,L,R)+16.
   \]
   For BB, the existing numeric-sum bound is (+3), and a direct constructor count gives length growth at most (+7). For DL, the run-zero and run-one branches each have net increase at most (+7); the run-two/right-run-(d) branch has net change (-1), because it consumes numeric mass (d+2) while adding (d+1) zero tokens; the remaining branches do not grow W. For CB, a direct case table gives the following upper bounds on the W increment: empty right side (+9); right zero (+15, the two bumps minus the consumed zero); right run-zero with tail empty/zero/run-zero/run-positive/repeat (+8/+7/+8/+7/+1); right run-one (+7); right run-two (+7); right run-at-least-three (+6); right repeat token (0). Thus (+16) is a safe uniform bound. The parameterized run-zero/right-run-((d+1)) branch has net change at most 7 after its consumed run pays for the (d) prepended zeros. The analogous MItem stepElemM branches have W_M-growth at most (+8), with the large prependZeroM branch again paid for by the consumed run.

4. **Sweeps.** The repository already proves
   - sweepCB_num_sum_bound: output numeric mass is at most input mass plus \(3|R|\);
   - sweepCB_length_bound: output token count is at most \(|L|+|R|+5|R|\).

   Consequently,
   \[
   W(\operatorname{sweepCB}(L,R))\le W(CB,L,R)+8|R|\le 9W(CB,L,R).
   \]

   A parallel induction on L for sweepBB should establish
   \[
   W(\operatorname{sweepBB}(L,R))
   \le W(BB,L,R)+8|L|+18
   \le 32(W(BB,L,R)+1).
   \]
   The constructor accounting is explicit: .run 0 moves to the right without changing W; .run 1 consumes one left token, adds a right run-zero, and applies bumpSymR, for net increase at most 8; .repB1 consumes its left token while eatB1 adds at most one right token and preserves mass; successful .rep2/.rep12 branches reinsert the stripped two-token prefix, with eatB2/eatB12R preserving mass and adding at most one token, again paid for by the removed left token. A failed .rep2/.rep12 branch peels with at most +2 mass and +5 length relative to the input, then stepElemBB adds at most +3 mass and +7 length, for net +17. The base, .zero, and .run(d+2) terminal branches use stepElemBB and cost at most +10. Thus there are at most |L| recursive +8 contributions and one terminal contribution at most 18. The missing mass lemmas for eatB2 and eatB12R follow from generic eatFuel_num_sum_le, since their blocks have positive mass.

5. **Finish-after-one-element.** Combining the atomic inequalities with the BB sweep bound should give
   \[
   W(\operatorname{stepElemThenBB}_{CB}(L,R))\le 256(W(CB,L,R)+1),
   \]
   and the analogous DL bound after peelL. The DL peelL itself raises \(W\) by at most 7.

## Macro-dispatch weight

After sweepCB, write S for numeric mass and T for token count before the sweep. The existing mass and length bounds give

\[
S_1\le S+3T\le 4W,\qquad T_1\le 6T\le 6W.
\]

The three successful macro outputs have simple mass/length bounds:

- **Rule A:** for the input stateA0(k,d) and output stateA(n-1,k-n,d-6n), the fixed literal mass rises from 6 to 9, while the three numeric fields change from \(k+d\) to \(k+d-6n-1\). Since the recognizer requires \(n\ge2\), total numeric mass actually drops by \(6n-2\). Its fixed left prefix grows by 6 tokens, so \(W_{\rm out}\le W_{\rm in}\).
- **Rule C:** with \(n=p-2\), the two increasing fields are \(k+2n\) and \(d+2n\), while the rep2 field falls to 2. Numeric mass rises by \(3n\le3S\), and the fixed prefix does not grow. Thus \(W_{\rm out}\le4W_{\rm in}\).
- **Rule B:** splitB2 counts copies of the literal block 011; each counted block has numeric mass 2. The output fields are \(p+2n-1\), \(1\), \(k-n\), and \(d+4n\), with \(n=m-1\). Comparing with the consumed input gives the exact numeric-mass change \(4n+1-p\), hence at most \(4S+1\). The output fixed prefix is at most 4 tokens longer (the input has one leading run-zero token, the (p) literal blocks, and the unchanged suffix). Thus \(W_{\rm out}\le5W_{\rm in}+8\).

A failed recognition uses stepElemThenBB_CB, already covered above. Hence the desired dispatcher inequality is

\[
W(\operatorname{afterSweepCB}(L,R))\le256(W(CB,L,R)+1).
\]

Combining this with the CB sweep gives the global target

\[
\boxed{W(\operatorname{stepSym}(s))\le 2^{12}(W(s)+1).}
\]

The BB and DL cases are smaller under the preceding bounds.

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

Let \(V=W+1\). The weight inequality gives \(V_{i+1}\le2^{13}V_i\). The literal initSymCyc3 states have:
- F424: \((|L|,\operatorname{numSum}L,|R|,\operatorname{numSum}R)=(13,52,9,85)\), hence \(W=160\);
- F412: \((13,52,10,86)\), hence \(W=162\).
Thus both satisfy \(W\le162<2^{10}\) and \(V_0\le2^{10}\).

For \(n\) symbolic transitions, the total primitive cost is then bounded by

\[
n\cdot2^{26}\cdot2^{26n}\cdot2^{20}
= n\cdot2^{26n+46}.
\]

The exact checkpoint chains give:

| Machine | Initial runElemFast steps | stepSym steps | SymRun exponent bound |
|---|---:|---:|---:|
| F424 | \(1+16+11\cdot256+4\cdot4096=19{,}217\) | \(70{,}511\) | \(2^{1{,}833{,}349}\) |
| F412 | \(7+3\cdot16+11\cdot256+4\cdot4096=19{,}255\) | \(21{,}383\) | \(2^{556{,}019}\) |

For the initial RLE prefix, \(W_M\) starts at 1 and each stepElemM raises it by at most 8. The F424/F412 rule tables have maximal variable costs \(3d+22\) and \(3d+20\), respectively (fixed branches are at most 13); since \(d\le W_M\), both are bounded by \(25(W_M+1)\). Thus the whole prefix is bounded by
\[
25N(8N+2)<2^{37}\qquad(N\le19{,}255).
\]
Add the initial entry costs (18 for F424, 1 for F412) and the separate final halting transition (+1 in each case); these are negligible relative to the prefix bound and do not affect the rounded bounds. Conditional total bounds are therefore:

- F424: fewer than \(2^{1{,}834{,}000}\) primitive steps;
- F412: fewer than \(2^{557{,}000}\) primitive steps.

**Reusable SymRun-phase corollary.** Under the same target lemmas, any SymRun phase with initial \(W\le2^{10}\) and at most \(2^{21}\) symbolic transitions has primitive cost below
\[
2^{26\cdot2^{21}+46+21}=2^{54{,}526{,}019},
\]
which is still far below \(2\uparrow\uparrow\uparrow5\). This criterion is independent of the detailed intermediate trace states; only the symbolic transition count and initial potential enter.

These are much weaker than the existing \(2^{463}\) and \(2^{193}\) candidates, but they are still sufficient for non-championship. Under the repository's published lower-bound convention \(2\uparrow\uparrow\uparrow5=2\uparrow\uparrow65536\), both are far smaller: \(1{,}834{,}000<2^{21}<2^{65535}\), and \(557{,}000<2^{20}<2^{65535}\).

## Formalization checklist and caveats

1. Prove the prependZeroSym/prependZeroM length and numeric-sum equalities, then the MItem and SymTok atomic combined-potential lemmas by cases (including the stepElemBB length bound +7).
2. Prove eatFuel length growth and the missing eatB2 / eatB12R mass bounds.
3. Prove the generic sweepBB potential bound.
4. Prove the Rule A/B/C output-potential bounds and afterSweepCB dispatcher bound.
5. Complete the costed afterSweepCB ReachesWithin wrapper using the existing pilot lemmas.
6. Instantiate the atomic cost envelope for F412. Its listed rule costs are no larger than F424's envelope, but a separate exact-source instantiation is still required.
7. Compile the exact imported source closure and audit transitive axioms before promoting any claim.

No Lean compile has been obtained for this route. The local shell and Python tools failed at the tool boundary during this invocation, and no CI run was dispatched under the repository's compile-first acceptance gate. The stronger trace-specific route remains intact; this note is an alternative intended to reduce dependence on its per-checkpoint range folds, not a replacement for any accepted result.
