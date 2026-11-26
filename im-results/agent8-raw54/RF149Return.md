# RF149 exact E-section reduction

**Scope:** frozen miss 149 of the Raw54 E0=1RF child, partial table `1RB1RE_1RC0RA_0RD0RA_1LD0LE_1RF0LE_1RB---`. The only unknown slot is F1. This is a paper reduction, not yet an original-source kernel theorem or a nonhalting decision.

## Exact representation

At an E0 section let the left half (excluding the scanned zero) be
(1^{m_1}0,1^{m_2}0\cdots 0,1^{m_k}), with each (m_i\ge1), or the empty word. Let (L=(m_1,\dots,m_k)), and let (R) be the right half, nearest first, padded by zeros. Seven live moves from the authentic blank configuration give (L=(), R=0011).

If the first right bit is 1 then the next transition is the missing F1. Otherwise consume that zero using E0,F0 (two live moves) and enter B with a nonempty run stack (W), obtained by adding 2 to the leading run of (L), or replacing empty (L) by (2).

At B, consume one bit. If it is 0, consume the C bit as well:
- C=0: enter D and consume its bit. On D=1 the return has left stack inc(W) and right word 0S, where S is the unconsumed suffix. On D=0, write two adjacent ones by the D0,D0 moves, clear the B0-written one with D1, and clear the leading m ones of W using E1. The return is (tail(W), 0^(m+1)11 S), with exactly 2+m further moves after consuming the D bit. If W has no further run, the next left cell is the implicit blank.
- C=1: enter A with flag e=1.
If the B bit is 1, enter A directly with flag e=0.

At A, consume its bit. On A=0, replace W by push(1, inc^e(W)) and resume B. On A=1, inspect the next bit: if 0, return with left push(1,inc^e(W)), right S (this inspection is not itself a live move). If 1, two E1 moves erase this one and the A1-written one; return with left inc^e(W) and right 00S.

Here inc increases the leading run by one. Every return has strictly positive cost and preserves the left-run grammar. The B/A forward loop consumes at least two right bits per iteration, hence must eventually exit on the implicit zero padding. The only undefined query before the next E0 is the initial F1 if the right word starts 1.

The grammar proof is by direct inspection of each written block: B1,A0 writes a separating zero and a new one; B0,C1,A0 adds a one to the previous run, writes a separating zero, and starts a new one-run. The A1 cases either retain the new run or erase it and restore the earlier run. D0 removes exactly one positive run and its preceding zero; D1 adds one to the head run. Thus no additional assumption on the left word is needed beyond the grammar.

## Computational evidence and remaining problem

Reproduced the frozen census digests ae1d7c235351d32702026c6d6d416d01548c257aab30e98773ea88b81d63113c and b5cc41348b6fb3a76c7abd71623b8b36f880a5c0579b7478df7c99b82d9e0461. The exact return implementation passed 10,000 random finite primitive-zipper regression cases (seed 149). The authentic macro run reaches 2,000,006 live steps, with 220,555 E returns and no F1 query. Frequencies: D0 109602; A0x 102652; yD1 5738; D1 661; yD0 659; A1x 546; xD0 391; A1y 153; xD1 152; yA1x 1. Here x denotes B0,C1,A0 and y denotes B1,A0. A0/A1 in terminal labels denote the bit inspected after A1. The observed at-most-one-loop condition is not a proved invariant.

The left stack is predominantly repeated run 4 with an initial run 8; the right half is predominantly repeated 00011 blocks with moving defects. Ordinary run-length and pair-run-block abstractions failed to yield a finite two-stack witness. The relaxation that forgets all left run lengths and permits arbitrary output 0^k11 at a D0 return is unsound as a nonhalting argument: its pushdown abstraction can reach F1 from the genuine entry. Preserve the exact left run stack correlation. A promising next step is pushdown saturation with right stack exact, abstract left **run-length** stack and exact multi-symbol macro transitions, refining only the first spurious pop or length choice.

No complete RF Cover or new global bound is claimed.