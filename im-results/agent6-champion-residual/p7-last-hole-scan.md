# Depth-7 one-hole sibling scan

The parent at depth 7 has exactly two undefined transitions, A/1 and B/1. Assigning any ordinary A/1 move other than the champion continuation 1RA leaves a one-hole partial machine with only B/1 undefined.

The bounded Node search in `search_p7_last_hole.mjs` classifies 23 children. It simulates at most 1,000,000 successful transitions, uses constant-memory Brent cycle detection, and then tries the bounded side-cycle search (entry ≤ 6, period ≤ 20, boundary radius ≤ 10) for any capped run.

## Reached B/1

These 15 children reach the remaining B/1 hole after the listed number of successful moves:

| A/1 move | Successful moves before B/1 |
|---|---:|
| 0RA | 464 |
| 1LA | 216 |
| 0LB | 214 |
| 0RB | 214 |
| 1LB | 214 |
| 1RB | 214 |
| 0RC | 706 |
| 1RC | 544 |
| 0LD | 242 |
| 0RD | 915 |
| 0RE | 1649 |
| 1LE | 3506 |
| 0LF | 218 |
| 0RF | 3312 |
| 1RF | 252 |

For each, the B/1 halt completion is a candidate last-hole leaf. Since the largest observed run is 3506, the remaining weighted-bound obligation is far below the champion score. These are computational candidates until the Lean first-hole replay and last-hole certificates are added.

## Not resolved by this bounded scan

The following eight children neither reached B/1 within one million successful moves nor yielded a side-cycle witness within the stated search bounds:

`0LA, 0LC, 1LC, 1LD, 1RD, 0LE, 1RE, 1LF`.

This is not evidence of nonhalting. They remain open and may require a stronger ray/cycle argument or a more efficient exact analysis.

The search run initially exhausted memory when it stored a million full configurations per machine. The current implementation uses Brent cycle detection with constant auxiliary configuration storage.
