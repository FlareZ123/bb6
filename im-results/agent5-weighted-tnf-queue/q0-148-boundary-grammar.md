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


## A genuinely local next-E hop (source-checkable, much stronger than the boundary return test)

A further exact checker computation for the original q0-148 partial table is

\`\`\`
knownRun p 13 <A, left=0, right=01110110>
 = <E, left=10101011, right=0>.
\`\`\`

The 8-symbol known-right prefix is enough. This is a *strictly local* move: all extra left/right tape tails are arbitrary and untouched. Compose it with \`firstRoundPositive\`: when the E1 right input is the final \`A=10\` of its current A-run **followed by a B=110 marker**, we have local right word \`010110\`, so the previous round leaves the exact input \`01110110\` for this 13-step transition. The Lean file now states

\`\`\`
markedHop(cs,L,R):
  run0 p (17 + 4 * scanCost(cs))
    <E, 10 ++ inputBits(cs) ++ 0 ++ L, 010110 ++ R>
  = <E, 10101011 ++ rightScanOutput(reverse cs) ++ L,
        0 ++ R>.
\`\`\`

This **does return to E1**, and establishes directly that the *new* E1 head has a zero as its immediate right neighbor. Its complete time is finite, explicit, and independent of the unspecified outer tape tails. \`markedHop\` is composed in Lean of original-table \`knownRun\` literals and inductive scanning lemmas. Source CI for the expanded file remains pending; the mathematical transfer identity follows from the exact finite local transitions above and the two list inductions.

### Gap-vector arithmetic for an E-hop

Let the entire tape word be \`A^g0 B A^g1 B ... B A^gm\`, with each inter-B gap at least one A, leading \`g0>=1\`. Suppose the head is at the **penultimate A** of group k with k<m, so there is exactly one A, then a B, to the right of this E head. Then \`cs\` encodes the prefix *before* the head and

\[
  \operatorname{scanCost}(cs)
    =2\sum_{i=0}^{k} g_i +3k-4.
\]

The marked hop changes the gap vector with **no change in the number of B tokens**:

\[
\begin{cases}
g_0\mapsto g_0-2,\quad g_1\mapsto g_1+3, & k=0,\\
g_0\mapsto g_0-1,\quad g_k\mapsto g_k-1,\quad
g_{k+1}\mapsto g_{k+1}+3, & k\ge1,
\end{cases}
\]

and leaves all other gaps unchanged. Its exact step count is

\[
 T_k=8\sum_{i=0}^{k}g_i+12k+1.
\]

The **new E head is the third A (zero-based index 2)** in the enlarged next group k+1. This is penultimate only when the old gap \`g_(k+1)=1\`. This indexing point is vital: requiring the new E to be penultimate in arbitrary long next groups would be false, despite the exact gap arithmetic above.

The remaining global proof must therefore handle three symbolic cases: (1) the marked hop with one A and a following B, now source-theorem candidate; (2) continuation within the *same* A-run when more than one A remains to the right of an E1 head; (3) boundary expansion when there is no B to the right. These cases appear algebraically sufficient to describe the infinite blank-tape trajectory, but they are not yet a closed invariant.

The current results are held in \`im-results/\`, not \`results/\`, because none alone resolves q0-148 or proves BB(6).


## A three-carry finite-state transducer for repeated blank-boundary sweeps (2026-11-28, proof candidates)

This materially narrows the last q0-148 rightmost-boundary difficulty. It concerns **source-defined parametric computations** on any chunk list, not an extrapolation of a long trace. The Lean proof candidates are now \`rightBlankTurn\`, \`rightBlankCarryShape\`, \`twoBlankTurns\`, \`anotherBlankCycle\`, \`ERightFirstMarker\`, and \`ARightToEOne\` in \`Q0148BoundarySweep.lean\`. The 3-carry word transformation is elementary and can be proved algebraically without Lean; source Lean CI compilation of the later compositions is still pending.

### Exact six-clause word algebra

Keep A = \`10\`, M = \`11010\` as **left-scan tokens**, and let their right-sweep outputs be \`O(A)=01\`, \`O(M)=01011\`. For any list \`cs\`, \`outSubst(cs)\` concatenates these outputs in the *original chunk order*. The right-sweep stack operation has the exact identity \`outputRightChunks(rightSequence(cs))=outSubst(cs)\`.

Scanning the word \`11 ++ outSubst(cs)\` leftward with full chunk tokens A/M leaves one of only THREE short residues. Let \`S=11\`, \`T=1101\`, \`U=1\`. The following six equalities of actual binary words define a deterministic transducer; the "output tokens" column contains full A/M tokens removed from the front of the concatenation:

| Carry | Input chunk | Output chunks | Next carry | Exact word equality |
|---|---|---|---|---|
| S | A | empty | T | \`11 01 = 1101\` |
| S | M | M | S | \`11 01011 = 11010 11\` |
| T | A | M | U | \`1101 01 = 11010 1\` |
| T | M | M A | S | \`1101 01011 = 11010 10 11\` |
| U | A | A | U | \`1 01 = 10 1\` |
| U | M | A A | S | \`1 01011 = 10 10 11\` |

The source-level second-turn pattern after the blank-right 13-step gadget is \`C0, left=0 ++ M ++ 11 ++ outSubst(cs) ++ (at least two blank zeros)\`. The transducer rewrites this **for every finite cs** as \`0 ++ inputBits(M::chunks') ++ residue ++ 00\`. Thus \`scanChunks\` applies at arbitrary length, and the residual is handled by one of exactly three finite source transitions:

| Residual carry | Left prefix in C0 | Steps | A0 right output |
|---|---|---|---|
| S (\`11\`) | \`01100\` | 4 | \`1010\` |
| T (\`1101\`) | \`0110100\` | 6 | \`011010\` |
| U (\`1\`) | \`0100\` | 3 | \`010\` |

This yields the **two full sweeps** source theorem candidate \`twoBlankTurns\` for any initial E1 left grammar chunk list \`cs\` and arbitrary untouched outer tails, as long as the explicitly read boundary cells are blank. At its end, qA0 is at the next left boundary, with right tape \`carryRight(residue) ++ outputBits(M::emittedChunks) ++ untouchedRightTail\` and exact finite duration
\[
  (4+4\,\mathrm{scanCost}(cs))+13+
    \mathrm{scanCost}(M::emittedChunks)+\mathrm{terminalCost}(residue).
\]

For carry T or U, that right prefix is respectively \`0 M\` or \`0 A\`, so the ordinary \`scanRightChunks\` transfers a new token plus all the prior chunks, a two-step blank-right turn returns to C0, and the **same** three-carry transducer applies again, this time to \`oldChunks ++ [newToken]\`. The general arbitrary-length lemma candidate is \`anotherBlankCycle\`; its input is **any** chunk list, and its output remains one of the same three carries. This closes a finite-state, *repeatable* abstract description of successive blank-boundary sweeps rather than treating each tape expansion as a new special case.

### Natural-number termination argument (conditional section)

Assume the initial left chunk sequence has a final marker followed by r copies of A: \`cs = prefix ++ [M] ++ A^r\`. The six-transition table proves directly, by induction on r, that the carry after scanning this final suffix is S if r=0, T if r=1, and U if r≥2. For r≥2, the emitted chunk list has a final M followed by exactly r−2 copies of A. Consequently, on a U carry, the next blank cycle reads one more A appended to a chunk list with r−2 trailing As, reducing the relevant counter to r−1. On a T carry, the next cycle appends M and resets the carry to S. Thus **the carry becomes S in at most r additional cycles**. The source E1→A0 initial two-sweep stage plus those finitely many cycles is universally finite.

At carry S, qA0's right tape begins \`1010\`, followed by the word \`outputBits(chunks)\`. Since each cycle's chunk list contains an M (its first token is M after the initial step), its \`outputBits\` ends with M; therefore the right tape contains a first M after a finite number n of A tokens. The original-source lemma candidates \`ERightFirstMarker\` and \`ARightToEOne\` execute this final qA0→E1 transition in exactly \`2n+6\` steps. In the resulting E1, the immediately right cell is zero, and **no F1 step occurred** during that conditional next-E computation.

This gives a concrete path to a universal **positive next-E return and F1 guard** for the boundary section whose leading A exponent is positive. It does *not* yet establish full nonhalting, because a succession of such next-E steps also requires proving the returned tape stays within a suitable global language (and handling intermediate E1 configurations). In particular, arbitrary syntactically valid boundary inputs can produce an E1 at a different active group; do not assume that first-return always resets directly to the group-0 phase. A complete source Cover still requires that closure theorem or a different global invariant.

**Reproducibility.** The exact-table regression \`q0-148-carry-transducer.cjs\` checks the first two-sweep source identity and the general additional-cycle identity across all chunk lists of length at most 9 (1,023 two-turn cases and 2,046 token/cycle cases), including all three carries. Run \`node im-results/agent5-weighted-tnf-queue/q0-148-carry-transducer.cjs\`. The mathematical finite-state and arbitrary-length list inductions, not the finite regression, are the relevant basis for any universal theorem. Until CI confirms the Lean theorems, this material remains in \`im-results/\`.
