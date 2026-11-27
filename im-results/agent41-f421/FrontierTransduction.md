# Exact F421 frontier transduction

**Status:** Exact paper derivation of a one-word return map for the authentic blank-root orbit; primitive replay corroborates it. No all-time avoidance invariant or nonhalting decision is established. `F421Frontier.lean` checks the return and its original-machine bridge in Lean. [F421FirstSeed.lean](F421FirstSeed.lean) instantiates them from the blank tape through the first secondary zero frontier.

Table: `1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---`. F1 alone is undefined. A frontier configuration has state D, left word u including the scanned bit in near-to-far order (zero padded), and right word 1 followed by blanks. The blank start reaches this frontier with u=11, head=1, in three transitions.

## Left scan

At D, the following disjoint prefix rules have arbitrary untouched left and right tails. Output is in leftward scan order, hence reversed on the right stack.

| Input | Output | Steps | Outcome |
|---|---|---:|---|
| 10 | 01 | 2 | D continues |
| 110 | 011 | 3 | D continues |
| 010 | 101 | 3 | D continues |
| 00 | — | 2 | B turnaround d |
| 011 | — | 3 | B turnaround e |
| 111 | — | 2 | F1 reached |

These form a complete prefix code on zero-padded input. Every continuing rule consumes a nonempty prefix and a finite-support word eventually presents 00. Let O concatenate the continuing outputs, and U be the untouched left tail after the terminal. At d the B head reads the reverse of X=1 O 1, with external left tail 1U; at e it reads the reverse of X=1 O 10, with external left tail 0U. In both cases X has length L equal to the total consumed prefix length. It starts with 1, contains no 00, and the initial B pair is respectively 11 or 01. These identities follow by literal application of the table: D00 writes 11 and turns through A0; D011 turns by D0, A1, C1. The terminal transition count and stack identity are direct table computations.

## Right scan

Write Bconf(T,s) for a B state with external left tail T and rightward stream s including the scanned bit, both zero padded. For arbitrary tails:

- Bconf(T,a1s) -> Bconf(0 (1-a) T,s) in 2 steps (a=0 or 1).
- Bconf(0T,10s) -> Bconf(001T,s) in 6 steps, through B1 C0 D0 A0 B1 C1.
- Bconf(T,empty) -> D(1T,[1]) in 2 steps.
- Bconf(T,1) -> D(0T,[1]) in 2 steps.

The initial normal pair creates the required left neighbor 0; every following pair again leaves 0 as the nearest external-left bit. Since X has no 00, the pairs exhaust the stream except for a possible final single 1. Thus there is no unbounded inner loop or hidden F1 access during the right scan.

## Return formula

Partition X from its right end, discarding its leading 1 if L is odd, into pairs p1,...,pN in the original near-left order, N=floor(L/2). Define f(10)=10, f(01)=01, f(11)=00. The terminal pair pN is 11 for d and 10 for e. Let t be 01 for d, 10 for e, and delta be 1 for even L, 0 for odd L. The new D word is

    u' = delta 0 f(p1) ... f(p(N-1)) t U.

Indeed each rightward pair writes the two bits of the accumulator as above; the following bounce replaces the earlier nearest 0 by 1 exactly when its reversed input pair is 01. Regrouping with the prepended 0 gives f, and the original external left bit gives the last replacement t. The right tape again has exactly one 1. The head advances 2 if L even and 1 otherwise. The number of primitive transitions in this return is L + 2N + 4b + 2, where b counts pairs p=01. A parse of 111 instead reaches the unread F1 row after the preceding continuing-block lengths plus two transitions.

Consequently deciding F421 reduces to the single authentic orbit of this finite-word transduction, starting with 11. An invariant avoiding the bad parse proves every completion of F1 nonhalting; finding the bad parse yields the exact first-use time by summing these costs. Neither has yet been established. The paired-prefix alphabet alone is insufficient because the untouched suffix may be misaligned.

## Reproduction

`frontier_map.py` implements the exact formula and independently executes primitive steps to compare the first 1,000 frontier returns, including full tape and cumulative time. The local replay matched through 711,352 primitive transitions, head 1968. This corroborates, but does not replace, the symbolic derivation above. The older two-billion-step simulation is not a proof of all-time avoidance.
