# D0=16, D1=18 final FAR holdout: unbounded doubling via a reusable prefix theorem

**Mathematical result, not yet kernel-accepted:** the literal table
`[8,1,11,0,11,13,16,18,10,22,23,4]`
never halts from the blank tape. This is the distinct V18 final row identified in [D16V17-PUMP.md](D16V17-PUMP.md). The argument below proves a positive return on an unbounded family, not just a large finite simulation. Lean candidates are Box28D16V18Growth.lean and Box28D16V18GrowthSource.lean; the local runtime returned ClientError before executing Python/shell, so neither has been compiled by this invocation. A complete D16 cut still requires the existing finite-tree consumer.

## Exact section algebra

Tape strings on both sides are **nearest-first**, with implicit infinite zeros after a finite suffix. The symbol under the head is separate. Write Q(k,S) for state E scanning 1, left `0 1^(k+2)` followed by zeros, right stream S. Write P(k,j,S) for E scanning 1, left `0 1^(k+2) 0 1^j` followed by zeros, right S. Thus P(k,0,S)=Q(k,S).

The code convention is 0=halt, other code 1+4q+2w+d with d=1 for right. The exact state table:

| state | 0 | 1 |
|---|---|---|
| A | 1RB | 0LA |
| B | 1LC | halt |
| C | 1LC | 0LD |
| D | 1RD | 0RE |
| E | 0RC | 0RF |
| F | 1LF | 1RA |

The three positive exact primitive macro identities (S arbitrary) are:

1. **Reset:** Q(k,0S) -> Q(0,0^k 11 S), cost k+25.
2. **Push:** Q(k,110S) -> P(0,k+2,S), cost 21.
3. **Transfer:** P(k,j+1,0S) -> P(k+2,j,S), cost 2k+19.

For (1) and (3), the common first five live steps are E1,F0,F0,F0,F1. They reach A scanning 1 with left `1^(k+2) L` and right `11 S`; L is the left tail of the original first unary run. Exactly k+3 A1 transitions then erase that run and the marker, reaching A scanning 0, right `0^(k+3) 11 S`. In (1) the left is blank; the next fixed 17 transitions are
A0 B0 C1 D0 D0 D1 E0 C0 C0 C0 C1 D1 E0 C1 D0 D0 D1.
Their endpoint is Q(0,0^k 11 S). In (3) the remaining left is `1^(j+1)`; the next six transitions are
A0 B0 C1 D1 E0 C1.
They reach D scanning 0, left `0 1^j`, right `0^(k+3)11 S`. The next k+4 D0 moves write ones across these zeros; the D1 move writes the separator and reaches P(k+2,j,S). In (2) the exact transition sequence is
E1 F1 A1 A1 A0 B0 C1 D0 D0 D1 E0 C0 C0 C0 C1 D1 E0 C1 D0 D0 D1.
This is a fixed local rewrite irrespective of the untouched left and right suffixes. Each macro is a genuine nonhalting prefix, not an abstraction that permits omitted transitions.

Iterating (3) j times gives P(k,j,0^j S) -> Q(k+2j,S). Consequently push followed by k+2 transfers yields the useful combined rule
Q(k,11 0^(k+3) S) -> Q(2k+4,S).
All these assertions concern arbitrary suffixes, not only the sampled blank trajectory.

## Prefix theorem and blank-root proof

Define g(0)=0, g(n+1)=2g(n)+4 (equivalently g(n)=4(2^n-1)).
For every n and every right stream S,
Q(0,0^g(n) S) ->* Q(g(n),S).
Proof by induction. At n=0 this is the empty prefix. Put k=g(n). The next prefix length is 2k+4:
- Consume its first k zeros by induction, leaving Q(k,0^(k+4) S).
- Reset once, giving Q(0,0^k 11 0^(k+3) S).
- Apply the same induction hypothesis with suffix `11 0^(k+3) S`.
- Apply the combined push-transfer rule to reach Q(2k+4,S).

From Q(g(n),blank), reset yields Q(0,0^g(n) 11 blank). The prefix theorem yields Q(g(n),11 blank). The combined rule (any finite zero prefix of blank is blank) then reaches Q(g(n+1),blank). The reset is positive, so each such return has positive primitive length. Direct execution of the first 17 live moves from the authentic blank start reaches Q(0,blank). Hence every finite primitive prefix is contained in a finite concatenation of successful return macros; the machine never queries B1, its only halt.

The proof establishes the verdict for this exact total table. It is not a universal verdict for the D0=16 parent, Raw10, or BB(6). The independent JavaScript primitive simulator checked 14,592 macro instances (k=2..39 in unshifted length, 64 arbitrary six-bit tails with final marker, and j=1..4) and the 17-move initial prefix. Those tests corroborate the local identities but are not the all-quantifier proof. The induction above supplies that proof; the Lean draft is separately subject to source-closure acceptance.
