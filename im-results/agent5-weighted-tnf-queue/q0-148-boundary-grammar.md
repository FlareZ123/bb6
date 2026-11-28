# q0-148: regular boundary language and a candidate first-return theorem (UNPROVED)

**Agent5, 2026-11-28.** Intermediate mathematical research; do not cite as a resolved source Cover. The open machine is exactly

\`1RB1LC_1RC0RE_0LA0LD_1LA0RF_1RB1RD_0RC---\`.

Its missing F1 entry would halt if visited. The strongest previous necessary guard was: on every E1 visit, the immediately right bit is 0. This note isolates a much larger regular **Poincare section** whose full positive-return property appears testable by symbolic sweeps rather than by unbounded whole-machine simulation.

## Candidate invariant

Let \`A := 10\`, \`B := 110\`, interpreted as ordinary left-to-right binary finite tape words; all cells outside the word are blank zeros. Let \`G\` be the family of words

\[
  W = A^{a} B A^{b_1} B A^{b_2}\cdots B A^{c},
  \qquad a\ge0,\quad b_i\ge1,\quad c\ge2.
\]

There is at least one \`B\`. Equivalently, a word belongs to \`(A|B)^*\` with at least one \`B\`, no adjacent \`B\` tokens, and at least two final \`A\` tokens. The initial control/head section is E reading 1, at the first bit of the last two \`A\` tokens. The head is therefore exactly two cells left of the **rightmost 1** of the word; the immediate right bit is 0.

**Conjectured first-return lemma:** From *every* such finite configuration, the defined q0-148 table performs a finite positive number of steps, never evaluates the missing F1 transition, and eventually revisits another E1 configuration of the same form (possibly with new word \`W'\` and translated tape interval). Moreover the new finite support starts and ends on the correct \`G\` word boundaries. The positive-return property, not just closure of a successor row, is required to deduce nonhalting by iteration.

A base case is established by the actual blank-start source trajectory: at time 147 it reaches E1 with finite word \`AAABAAAA\` (binary \`10101011010101010\`) and the head on the first 1 of the last two A's, with zeros outside. This finite-step fact can be checked directly from the machine table; no Lean certificate for this lemma has yet been submitted.

## Why this appears stronger than short local context

The observation arose from decoding complete tape words at **all** E1 visits in a 5,000,000-step forward simulation of the exact table. At 1,220 E1 occurrences, the whole finite support plus one trailing zero parsed as \`(A|B)*\`, adjacent \`B\` tokens did not occur, the E1 head was always on the first bit of an \`A\` token, and the number of \`B\` tokens was odd. The same observation was seen at every boundary hit, where the E1 head sits two cells left of the last 1. This is exploratory evidence, not an induction.

In particular, every E1 observation had *no* tape occurrence of \`111\`, even though intermediate control states transiently create triples. The same run had a maximum of three simultaneous \`111\` occurrences and a maximum 1-run length of five in a 16,000,000-step separate sample; these maxima have **not** been proved globally.

### Reproducible finite search

The independent script \`q0-148-boundary-grammar.cjs\` exhaustively creates all \`G\` inputs with 1–4 B tokens, leading A exponent 0–4, each interior A exponent 1–4, and final A exponent 2–6. For each it runs the *exact* machine until the first E1 at the tracked right boundary (or a 200,000-step cutoff), then checks the returned tape word, physical rightmost-1/head relation, and grammar. **All 2,125 cases returned to the section with no F1 visit**, each in at most 35,364 steps. There were zero caps. Run:

\`\`\`sh
node im-results/agent5-weighted-tnf-queue/q0-148-boundary-grammar.cjs
\`\`\`

A separate test of 450 randomized \`G\` inputs (more B tokens, random gaps 1–8, leading gap 0–4 and terminal gap 4) also returned with no guard violations; varying the terminal gap over 2–12 on 990 more random cases preserved token separation. Neither finite test proves the universal return statement.

**Negative control for the *weaker* grammar:** if adjacent \`B\` tokens are allowed, the input word \`101101101010101101101101101101101010\` with E head at fourth-last cell enters the missing F1 slot after 628 steps. Its A-gap decomposition is \`[1,0,3,0,0,0,0,0,2]\`, explicitly violating the positive interior-gap condition.

## Proof work needed

The central missing piece is a symbolic **first-return theorem for arbitrary exponents and number of B tokens**, not a longer finite run or another local-radius BFS. The machine visibly performs repeated left-sweeps via the transparent \`C0 -> A1 -> C0\` alternation across long \`10\` regions; the \`C1 -> D0 -> A1\` sequence processes a double-one marker. Derive a finite set of parametric tape-rewrite and sweep lemmas that (i) never trigger F1, (ii) terminate an entire epoch, and (iii) preserve at least one A separator between consecutive B markers and the final two A tokens. Once established, compose the 147-step blank-start bridge and the positive-return invariant to obtain a source Cover for q0-148. The hypothesis is regular as a *set of section configurations*, but its Turing-machine return function may involve unbounded arithmetic and should not be assumed a finite-state transducer without proof.

This approach is independent of the bounded SMT two-stack automata search; the latter had no certificate for DFA pairs up to 4x4 and single-sided composed FAR at d6–7 was UNSAT for q0-151. Do not classify q0-148 as nonhalting until the parametric return theorem is fully proved.


## Explicit symbolic sweeps (new proof candidate; CI axiom audit pending)

The source file \`Q0148BoundarySweep.lean\` constructs the following **universally quantified** computations using the original partial table and the trusted \`Agent31Pump.Auto.knownRun_sound\` and \`Agent5PackedSweep.sweepLP/sweepRP\` transfer frameworks. All terms are ordinary two-sided tape-stack configurations with unknown tails \`L,R\`.

- In state C reading 0, a **leftward** \`10\` transfer costs 2 steps and leaves the transferred two symbols unchanged in near-head stack order:
  \`knownRun p 2 <C, left=010, right=empty> = <C,left=0,right=10>\`.
- In state C reading 0, a **leftward** separated-marker \`11010\` transfer costs 5 steps:
  \`knownRun p 5 <C,left=011010,right=empty> = <C,left=0,right=11010>\`.
  In geometric tape order this is the local rewrite **\`0 AB \` to \`0 BA\`**, where A=10, B=110. Thus a left scan moves a B marker left across its preceding A separator without inspecting other cells.
- In state A reading 0, a **rightward** \`10\` transfer (after fixed right zero) costs 6 steps and emits \`01\` on the left:
  \`knownRun p 6 <A,left=0,right=010> = <A,left=001,right=0>\`.
- A **rightward** \`11010\` transfer costs 15 steps and emits the reversed \`01011\`:
  \`knownRun p 15 <A,left=0,right=011010> = <A,left=001011,right=0>\`.
- The E1 entry is an exact three-step local computation:
  \`knownRun p 3 <E,left=10,right=010> = <C,left=0,right=1110>\`.
  This turns the last two A tokens into a temporary 1110 sentinel on the right. At the leftmost boundary, there are two exact terminal transfers: \`C, left=00\` -> \`A,left=0,right=0\` in 1 step; \`C,left=01100\` -> \`A,left=0,right=1010\` in 4 steps. They account for leading A exponent positive and zero, respectively.

Define \`LeftChunk := A | M\`, with near-left stack encoding \`bits(A)=10\`, \`bits(M)=11010\`, cost 2/5. For an arbitrary **list** of chunks \`cs\`, \`scanChunks\` is proved by list induction from the two exact one-block transfer lemmas. It consumes all chunks leftward, reverses their order onto the right stack, never touches arbitrary outer tails, and runs in exactly \`scanCost cs\` steps. The analogous \`scanRightChunks\` consumes chunks rightward at cost 6/15 per block and reverses each block's near-stack orientation.

The two **full leftward turn** lemmas are the central result candidates (in source, with arbitrary \`cs,L,R\`):

\`\`\`
halfSweepPositive:
  run0 p (3 + scanCost(cs) + 1)
    <E, 10 ++ inputBits(cs) ++ 0 ++ L, 010 ++ R>
  = <A, 0 ++ L, 0 ++ outputBits(cs) ++ 1110 ++ R>

halfSweepZero:
  run0 p (3 + scanCost(cs) + 4)
    <E, 10 ++ inputBits(cs) ++ 1100 ++ L, 010 ++ R>
  = <A, 0 ++ L, 1010 ++ outputBits(cs) ++ 1110 ++ R>
\`\`\`

The positive-leading branch naturally applies to a checkpoint word \`A^a B A^b1 ... B A^c\` with a≥1, internal gaps≥1 and c≥2. Construct \`cs\` from the **rightmost** c−2 A blocks, then one M block and b_last−1 A blocks, etc., ending with the first M and a−1 A blocks. The total transfer cost is \`|W|−4\` (there are \`|W|−4\` symbols in those chunks), so the E→left-boundary turn takes exactly **\`|W|\` steps**. For a=0, omit the first unguarded B from the chunk list and use \`halfSweepZero\`; that turn also takes **\`|W|\` steps**. Both cases avoid F1 by construction. They specify the resulting tape, rather than merely its runtime.

The first **bidirectional** formula for positive leading gap is also in Lean source as \`firstRoundPositive\`, using reversed chunk order and the identity \`rightScanCost = 3 * scanCost\`:

\`\`\`
run0 p (4 + 4 * scanCost(cs))
  <E, 10 ++ inputBits(cs) ++ 0 ++ L, 010 ++ R>
 = <A, 0 ++ rightScanOutput(cs) ++ L, 01110 ++ R>
\`\`\`

This is the exact symbolic round ending at the **right-hand 1110 sentinel**, at time \`4|W|−12\` for \`|W|=scanCost(cs)+4\`. Every step is source-defined. It does **not** yet prove how the sentinel is processed, nor that another checkpoint is reached. The remaining mathematical task is a parametric right-edge gadget/return argument (possibly multiple alternating sweeps) that maps the resulting configuration back into \`G\` after finitely many steps.

These derivations were checked independently against the exact transition table and committed to native Lean with \`#print axioms\`, but this note deliberately withholds the phrase "Lean verified" until GitHub Actions compilation succeeds. They are strictly intermediate and do not close the source leaf.
