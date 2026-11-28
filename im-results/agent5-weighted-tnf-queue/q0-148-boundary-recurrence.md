# q0-148: an explicit boundary-to-boundary arithmetic recurrence and an inductive invariant

**Agent5, 2026-11-28 ~04:27 UTC. Status: mathematically proved *closure of the abstract recurrence*, but the source-to-recurrence correspondence is still a CONJECTURE; the one-hole machine remains unclassified.** This is intermediate research in \`im-results/\`, not an accepted source Cover.

## Exact source table and encoding

Machine \`1RB1LC_1RC0RE_0LA0LD_1LA0RF_1RB1RD_0RC---\`; the undefined entry is F1. Let \`A = 10\`, \`B = 110\` be binary words. For a finite vector

\[
  g=(a,g_1,\dots,g_{m-1},4)
\]

define the finite binary tape word

\[
  W(g)=A^a B A^{g_1} B\cdots B A^{g_{m-1}} B A^4 .
\]

The head is E reading 1, positioned at the **penultimate A token** (zero-based A index 2) of the final \`A^4\`. All outside cells are 0. There are exactly \`m\` B tokens, and \`m\` is odd.

## Proposed stable boundary grammar \`P(g)\`

There is a finite exceptional base vector \`(3,4)\` with m=1. In the stable case m≥3:

1. m odd; a is either 1 or 3; each g_i (1≤i<m) is an odd integer at least 3; the last entry is 4.
2. Adjacent interior gaps weakly descend in steps of 0 or 2, so \`g_i-g_(i+1)∈{0,2}\` for every 1≤i<m−1.
3. The penultimate gap is 3 or 5: \`g_(m-1)∈{3,5}\`.
4. Crucial **head-height constraint**: \`g_1∈{m+a−3, m+a−1}\`.

This is a strikingly narrow infinite class of arbitrary-width tapes. In a 14-million-step exact source trace from blank, all **58 observed right-boundary E1 checkpoints** satisfied \`P\`, including the first exceptional (3,4). The non-increase differences were 980 zeros, 879 twos, and **zero** other values among the observed m≥3 checkpoints. A numerical trace, of course, does not prove the pattern.

## Conjectured exact TM boundary-to-boundary map \`F\`

For the exceptional source base, one entire boundary epoch has

\[
  F(3,4)=(3,3,3,4).
\]

For every stable vector \`g=(a,g1,...,g_(m-1),4)\`, define

\[
 a'=\begin{cases}g_1-m+3,&a=1\\g_1-m+1,&a=3,\end{cases}
 \qquad
 m'=\begin{cases}m,&a=1\\m+2,&a=3.\end{cases}
\]

Then the predicted **first positive return to any right-boundary E1** is the complete vector

\[
F(g)=
\begin{cases}
(a',g_2+2,\dots,g_{m-1}+2,5,4),&a=1,\\
(a',g_2+2,\dots,g_{m-1}+2,5,3,3,4),&a=3.
\end{cases}
\]

There are exactly m' B tokens in the returned word, the head again at A-index2 in terminal \`A^4\`, and no visit to the F1 hole on the finite run. This is a **strong parametric conjecture about the original Turing machine**, not a theorem yet. Unlike generic never-halt invariants, it predicts the *entire next tape* exactly, including how the number of markers changes.

**Exact-source evidence:**
- 138 randomly generated stable vectors satisfying all four conditions (m 3,5,7,9,11) were simulated to the *first* next boundary with the original partial table; all 138 returned precisely \`F(g)\`, without a halt or cap (max 9,644 steps).
- Another independent 650 random vectors of the weaker odd interior-gap shape (a∈{1,3}, odd m1..9, arbitrary odd gaps≥3) matched the corresponding **first positive E1** formula, including the detailed group/head index, without a halt or cap.
- A deterministic exhaustive regression of \`P\` through m=11, testing every possible 0/2 adjacent interior-gap difference, is encoded in \`q0-148-boundary-recurrence.cjs\`. The code validates \`P(g)\`, constructs exact binary source tape words, runs original transitions, detects the next boundary via the physical **rightmost written 1**, parses the entire output tape and compares every gap and head position to \`F(g)\`. At this writing the all-input CI run has **not** been observed completed; do not claim its full count as executed.
- \`q0-148-boundary-return.cjs\` separately tests the **first** next E1 update over all small odd-marker structures and a reproducible xorshift32 population.

## A fully mathematical result: the abstract recurrence preserves \`P\`

**Proposition.** Let \`P(g)\` be the arithmetic grammar above. Then \`P(3,4)\` is the exceptional base and \`F(3,4)\` satisfies the stable grammar. For every stable \`g\` satisfying \`P\`, \`F(g)\` also satisfies the stable grammar. This is unconditional elementary arithmetic about finite vectors (independent of any TM semantics).

**Proof.** For m≥3, the head-height condition \`g1∈{m+a−3,m+a−1}\` forces \`a'∈{1,3}\` by substitution. m' is m or m+2, so remains odd ≥3. All new interior gaps are odd≥3: \`g_(i+1)+2\` remain odd≥5 and the appended entries are 5 and optionally 3,3. The new penultimate gap is 5 when a=1 and 3 when a=3, hence lies in {3,5}.

The adjacent interior-gap differences of all the shifted entries are \`(g_(i+1)+2)−(g_(i+2)+2)=g_(i+1)−g_(i+2)∈{0,2}\`. At the join, the old penultimate gap \`g_(m-1)∈{3,5}\` gives \`(g_(m-1)+2)−5∈{0,2}\`. In the a=3 branch, the new end \`5,3,3\` contributes differences 2,0. So the difference constraint is preserved.

It remains to check the new head-height condition. The leading new interior gap is \`b1=g2+2\`. The old interior difference constraint \`g1−g2∈{0,2}\` gives \`b1∈{g1,g1+2}\`. Meanwhile

\[
  m'+a'−3 = g_1
\]

in **both** branches: if a=1 then \`m'=m,a'=g1-m+3\`; if a=3 then \`m'=m+2,a'=g1-m+1\`. Therefore \`b1∈{m'+a'−3,m'+a'−1}\`, as required. The base output \`F(3,4)=(3,3,3,4)\` has m=3,a=3,g1=g2=3, satisfies all conditions. QED.

This is an **induction-ready invariant** once the original-source boundary return lemma has been established:

\[
\forall g\;[P(g)\implies\operatorname{RunDefinedToNextBoundary}(g,F(g))].
\]

Given that universal lemma, the blank-to-boundary bridge at step147 and the proposition above imply an infinite sequence of positive-length source transitions, and hence the machine can never reach its missing F1 entry. A Lean-checkable \`NeverHalts\` theorem would close the q0-148 F1 source leaf.

## Why a full parametric source proof looks attainable

The existing \`Q0148BoundarySweep.lean\` supplies exact source finite local gadgets and unrestricted list-induction tape sweeps; more importantly, it decomposes the blank-right boundary into a **three-state carry transducer** with residues S=11,T=1101,U=1, and six bit-string equalities describing all A/M tokens. For a boundary vector in \`P\`:

- Read the left tape from head to the left edge as a chunk list \`cs = A^2 M A^(g_(m-1)-1) M ... M A^(g_1-1) M A^(a-1)\`. Every interior exponent after a marker is even (because its gap was odd). The final A exponent is either 0 or2.
- The six-clause transducer shows that processing each \`A^(2k) M\` returns carry S, and processing the terminal \`A^(a−1)\` leaves carry **S for a=1** or **U for a=3**. For a=3, two more boundary cycles yield S. Thus the **number of additional blank-boundary cycles is exactly 0 or 2**, independent of marker count, under \`P\`. This is much stronger than a generic well-founded trailing-A countdown.
- The final A0→E1 marker sweep sends the new E head into the leftmost group, at position **g1+2**. On this first E1 return the new gap vector is
  \`(g1+g2+3,g3,...,g_(m-1),3,1,1)\` if a=1, or the same with four trailing 1s if a=3. (Here the **old** g1,g2 are used; this first-return formula was directly tested on 650 nonboundary-grammar odd-gap cases.)
- For each further group \`k<m'\`, the source \`markedHopN\` macro (already in the Lean file) advances active E1 one marker rightward, with exact local gap rule. At group0, j is the E-head A index and n is the number of extra As before the next marker; update \`g0:=j, g1:=g1+n+3\`, and active index in next group becomes \`n+2\`. For group k≥1 update \`g0:=g0−1, gk:=j+1, g_(k+1):=g_(k+1)+n+3\`, again with next index n+2. These are **positive finite source runs**; the missing F1 is never evaluated.
- Iterating the group-hops across each of the m' markers and simplifying gaps yields exactly the vector \`F(g)\` above. Every source epoch therefore consists of 0 or2 blank-boundary cycles followed by a finite sequence of marked E-hops. What remains is a *source-proof* that all intermediate tape shapes and boundary padding match the Lean macro hypotheses, then a formal or paper-proof link between the micro-step semantics and \`F\`.

The outstanding proof obligation is now **narrow and precise**. Do not continue blind simulations: formalize \`P\`, the list-of-chunks structure, the S/U carry result for the even gap sequence, the 0/2 blank-turn recurrence, and the iterated \`markedHopN\` arithmetic. Those suffice to aim for a direct source nonhalting proof. The source macro file is still waiting for CI to compile its newest whole-cycle lemmas; syntax/typechecking errors do not count as disproving this arithmetic theorem, but those macros cannot be cited as formally verified until the kernel accepts them.


## Exact source step-count formula for the first boundary reset (derived from the macro costs)

Let \`N=|W(g)|=2(a+g1+...+g_(m-1)+4)+3m\` be the length in tape cells of a stable boundary word. The source macro decomposition above yields an unexpectedly simple **exact predicted step count to the first next E1**, not yet the next boundary:

\[
 T_{\mathrm{reset}}(g)=
 \begin{cases}
  5N+2g_1+10, & a=1,\ m\ge3,\\
  13N+2g_1+66, & a=3,\ m\ge3,\\
  293, & g=(3,4)\ (\text{base }m=1).
 \end{cases}
\]

Explanation from literal original-source gadgets, conditional on the all-length compositions:
- Write \`s=scanCost(cs)=N−4\`. The qE1→right sentinel round costs \`4+4s\`; the 13-step blank-right reversal yields qC0.
- For **any** initial carry S/T/U, the source all-length left scan and terminal left reversal together cost \`s+9\` steps. Indeed bit-length conservation in the six binary carry equalities gives the emitted chunk-bit length \`s+2−length(carry)\` and the leading M adds 5, while the finite source terminal cost is \`length(carry)+2\`. Thus the first two bidirectional turns cost \`4+4s+13+s+9 = 5N+6\`, **independently of marker count or carry**.
- If a=1, the carry after those two turns is S, and A0's right tape begins \`A^(g1+1) B...\`. Its exact source A0→E1 sweep takes \`2g1+4\` steps, producing \`T_reset=5N+2g1+10\`.
- If a=3, the initial carry is U. The next complete blank-boundary cycle has token-word length \`N+4\` and takes \`4(N+4)+6=4N+22\` steps, yielding carry T. The next cycle has word length \`N+7\` and takes \`4(N+7)+6=4N+34\` steps, yielding S. (The general cycle cost \`4t+6\` for an input chunk list of bit length t follows by \`rightScanCost=3t\`, two blank-right steps, transducer-conserved emitted length \`t+2−length(carry)\`, and terminal cost \`length(carry)+2\`.) Finally A0→E1 takes \`2g1+4\` steps. Sum = \`13N+2g1+66\`.
- For the exceptional base g=(3,4), N=17 and the first marker sits after four A tokens instead of g1+1; the final A0→E1 sweep costs 10, not 12, so \`5N+6+(4N+22)+(4N+34)+10=293\`. This matches the exact blank source E1 event at source time 147+293=440.

For a source E1 active at group k<m on A-index j, with g_k≥j+2 and \`n=g_k−j−2\` even, the generalized source marked-hop time is likewise explicit:

\[
 T_{\mathrm{hop}}(g,k,j)=
    13 + 8\sum_{i<k}g_i + 6j + 2g_k + 12k
\]

since the left scanned word uses \`2Σ_(i<k)g_i+2j+3k\` cells and the right continuation uses \`13+2n\` steps. After the hop, active group increments k→k+1; the next E1's head index is \`n+2\`. For k=0 the new leading gap is j; for k>0 the leading gap drops by1, active gap k becomes j+1, and next gap gains n+3. This is an exact *finite source computation* whenever the corresponding parametric macro's explicit stack/tail hypotheses are met.

These formulas provide an explicit natural-number witness for every source return. Once the structural word-matching and macro compositions are typechecked, an induction proof of nonhalting does not need an abstract termination argument or potentially noncomputable search for return times.
