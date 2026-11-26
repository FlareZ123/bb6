# Residual 2040: all completions are nonhalting

**Status:** complete mathematical proof over the ordinary two-symbol Turing transition semantics; original-source Lean integration is not yet checked. This decides the exact one-hole residual, not the six-hole E0=0LF parent.

The machine is `1RB1RA_1RC0RB_1LD0RD_---0LE_0LF1RC_1LA1LF`, or `[7,3,11,5,14,13,24,16,20,11,2,22]` in the repository's code convention. Only D0 is unspecified. The proof shows D0 is never queried, so it applies to every completion, including the completion that halts at D0.

## First-exit lemma

Write (A(h;n,c)) for state A with head at cell h, and tape from h rightward equal to

    0 1^n 00 1^c 0^omega

where n >= 1 and c >= 2. The tape strictly left of h is arbitrary. Define f and delta by

| n mod 4 | f(n) | delta(n) |
|---|---:|---:|
| 1 | n+1 | +1 |
| 2 | n+3 | -1 |
| 3 | n | +2 |
| 0 | n+2 | 0 |

**Lemma.** From A(h;n,c), a finite positive number of ordinary moves reaches state F at h-1, with tape from h rightward equal to

    1^(f(n)-1) 00 1^(c+delta(n)) 0^omega.

Before this exit, no transition reads a cell strictly left of h, and no transition reads D0. The first exit is an arrival in F at h-1; its transition has not yet executed. In particular this is a local lemma, independent of the unknown left prefix.

### Two elementary runs

(I) Starting A on `0 1^b 00 1^c` (b >= 1), A0 writes 1; B erases the b ones and B0 writes 1 at the first delimiter zero; C0 writes 1 at the second delimiter zero and moves left; D1 erases the first delimiter cell and E0 moves left into F. Thus F is at h+b-1. The tape from h is `1 0^(b+1) 1^(c+1)`. For b=1, F is already at the initial cell h, reads 1 and exits at h-1. For b=2, F0 writes 1 and returns A to h, where the suffix is `11 00 1^(c+1)`. For b>=3, F0 writes 1 and returns A at h+b-2 with suffix `0 1 00 1^(c+1)`; the tape between h and this new head is exactly `1 0^(b-3)`.

(II) Starting A on `1^b 00 1^c` with b>=1, c>=2, A scans its b ones and writes 1 in the first delimiter; B0 writes 1 in the second. C1 and D1 erase the first two terminal ones; E0 enters F on the second newly written 1. F scans left over all b+2 ones and arrives at h-1. The new suffix from h is `1^(b+2) 00 1^(c-2)`. All D queries in both elementary runs are D1. Both runs are finite; their only possible read outside the indicated interval would be the next, not-yet-executed F transition after exit.

### Strong induction on n

For n=1, (I) gives the claimed first exit, f=2 and delta=1. For n=2, (I) returns to A on `11 00 1^(c+1)`; (II) gives f=5 and delta=-1. It is safe since c+1>=3.

For n>=3, (I) leaves A at h+n-2 with suffix `0 1 00 1^(c+1)`, preceded within the old interval by `1 0^(n-3)`. While there are at least two trailing zeros in this prefix, apply the inductive first-exit lemma to the current suffix, of run length m and tail length t. F arrives one cell to its left on the last zero; F0 writes 1 and moves A one more cell left, onto the preceding zero. This consumes exactly two prefix zeros and changes the suffix parameters to (f(m), t+delta(m)). It does not alter any earlier prefix cell. Starting from (1,c+1), after 2j such applications the pair is (4j+1,c+1), and after 2j+1 it is (4j+2,c+2). This follows directly from the two corresponding residues in the table. Every call has run length strictly less than n and tail length at least c+1, so the strong induction hypothesis applies.

After floor((n-3)/2) applications, the remaining prefix is either 1 or 10. The exact boundary values are:

| n mod 4 | remaining prefix | current m | current t |
|---|---|---:|---:|
| 3 | 1 | n-2 | c+1 |
| 1 (n>=5) | 1 | n-3 | c+2 |
| 0 | 10 | n-3 | c+1 |
| 2 (n>=6) | 10 | n-4 | c+2 |

All four m are positive and smaller than n. Apply the inductive first-exit lemma once more to this current suffix.

* If the prefix is 1, F arrives at h on that 1 and executes F1, arriving at h-1. The run length from h is f(m), and the tail length is t+delta(m). Substitution in the two odd rows gives respectively (n-1,c+2) and (n,c+1), precisely (f(n)-1,c+delta(n)).
* If the prefix is 10, F arrives at h+1 on 0, writes 1 and moves A left to h on the original 1. Its suffix is `1^(f(m)+1) 00 1^(t+delta(m))`. In both even rows the tail before (II) is at least c+1>=3. Apply (II) to obtain first exit at h-1, with run length f(m)+3 and tail length t+delta(m)-2. These are (n+1,c) and (n+2,c-1), respectively, again the required (f(n)-1,c+delta(n)).

This completes the strong induction. The finite composition is entirely within cells >=h until the first exit, and never queries D0.

## Authentic blank orbit

The blank initial run is exactly the following nine moves. The table lists the state/head and all cells containing 1 after each move.

| moves | state | head | ones |
|---:|---|---:|---|
| 0 | A | 0 | empty |
| 1 | B | 1 | 0 |
| 2 | C | 2 | 0,1 |
| 3 | D | 1 | 0,1,2 |
| 4 | E | 0 | 0,2 |
| 5 | C | 1 | 0,2 |
| 6 | D | 0 | 0,1,2 |
| 7 | E | -1 | 1,2 |
| 8 | F | -2 | 1,2 |
| 9 | A | -3 | -2,1,2 |

Thus the machine reaches A(-3;1,2) with all cells to the left blank. Apply the first-exit lemma. F at h-1 reads blank, writes 1 and moves A to h-2, where the left prefix is still blank. This yields A(h-2;f(n),c+delta(n)). In particular the two-step section cycle on parameters is

    (4k+1,2) -> (4k+2,3) -> (4k+5,2),  k >= 0.

Both input tails satisfy c>=2. Every return executes finitely many positive ordinary moves, so arbitrary numbers of these returns produce arbitrarily long actual blank-run prefixes without any D0 query. Therefore no compatible completion can halt.

The result is a paper-level proof of the residual's universal nonhalting and hence of its weighted bound zero. The exact original-source Cover must still be formalized and compiled before consumption into the parent certificate.
