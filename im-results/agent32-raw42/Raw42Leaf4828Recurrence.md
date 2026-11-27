# Exact run-counter reduction of Raw42/1LB leaf 4828

Agent 32, 2026-11-27. **Mathematical reduction, not a halt/nonhalt verdict.** This is the one remaining unclassified open discovery leaf of 1LB (other than the now locally checked 18612). Exact table `1RB0RF_1RC1LB_0RD0RE_1LD0LB_0RA0LD_---0RD`. Undefined F0 is the only hole. The exact return rules below are derived directly from the literal table; formal source transport has not yet been compiled.

## Seven exact B0 rules

At state B scanning a zero, let L and R be the infinite sequences of nonnegative lengths of runs of ones between successive zeros, starting immediately to the left and immediately to the right of the scanned zero respectively (both nearest first). All but finitely many entries are zero. Use finite lists with implicit zero extension and trim terminal zero entries. Write L=(k,L'), R=(a,b,c,T); T may be empty. Here a,b,c are the first three run counts, with missing entries zero. A right word with counts (a,b,c,...) is 1^a 0 1^b 0 1^c 0 ... .

The following paths reach another B0 or the undefined F0 query:

| Condition | New L | New R | Defined steps |
|---|---|---|---:|
| a=0 | L' | (k+b,c+2,T) | 4b+k+5 |
| a>=2 | L' | (k,1,a-2,b,c,T) | k+5 |
| a=1,b=0,c=0 | (1,0,k+1,L') | T | 4 |
| a=1,b=0,c>=1 | (0,k+1,L') | (c+1,T) | 6 |
| a=1,b=1 | F0 query | | 4 |
| a=1,b=2 | L' | (k,c+5,T) | k+11 |
| a=1,b>=3 | (0,0,k+1,L') | (b-3,c+2,T) | 4b-1 |

Proof: A0 at the blank root goes to B0 after one defined step with L=(1), R=empty. At each B0 write a one, move right C. If the right word starts 01, C0 then D1 rewrites it to 00, moves back to its first zero in B, and prepends one to L. This repeats b times when a=0. At the resulting 00 prefix C0, D0, D0, D1 fill the two right zeros and erase the saved B cell, reaching B immediately to its left. B1 sweeps the k+b left ones back onto R before the next B0. Total 3b+5+k+b. If the right prefix is 11, C1,E1,D0,D1 erase the B cell and rewrite the two bits to 10; the left sweep gives the second rule. If the prefix is 100, C1,E0,A0 leave the original B cell and the new A cell as ones with two zeros between; the next bit determines a B0 immediately or a two-step B1 retreat. If the prefix is 1010, the four defined transitions B0,C1,E0,A1 reach F0. If the prefix is 1011, F1 clears its scanned one and moves right D. When the next bit is zero, D0 fills it and the four erased cells to its left; D1 erases the saved B cell and B1 sweeps the k ones, giving the sixth rule. When the next bit is one, D1 clears it and moves left to B0, with left (0,0,0,k+1,L') and right (0,b-3,c,T). Apply the a=0 rule to this endpoint; total 6+4(b-3)+5=4b-1. Every path works with arbitrary untouched tails, and with implicit blank extension. Thus no simulation horizon is needed for the reduction, and no unassigned transition is used except the explicitly identified terminal query.

## Deferred-counter transducer (conditional normal form)

After the first a=0 rule the exact blank orbit is at B0 at time 7 with L empty and R=(1,2). Positive-counter lists below omit the marker 1 in R. A normal section P has L empty and R=(1,b,c,d,...), b,c,d,... all >=2. A deferred section Q has L=(0,0,s_1,0,s_2,0,...,s_m), all s_i>0, and the same right form. Write D=(s_m+1,...,s_1+1) for the deferred output in far-to-near order (empty at P). Require b>=8 at Q; this is a **sufficient guard to be proved**, not an observed fact elevated to a theorem. Let b=3q+r, r in {2,3,4}. Put absent c,d equal to zero.

- r=4: enter Q with deferred list D followed by q+2 and right positive list (c+2q+2,d,...).
- r=3: return to P with right list (D,q+2,c+2q+2,d+2,remaining after d).
- r=2, q>=2: return to P with right list (D,q,c+2q+5,d,...).
- r=2, q=1: necessarily P under the guard, return to P with list (c+7,d,...).
- r=2, q=0: necessarily P under the guard, return to P with list (c+5,d+2,remaining after d).

Derivation: when the first right count is 1 and b>=5, the last rule above followed by the a>=2 rule and the a=0 rule effects one transfer b->b-3, c->c+2, and increments the leading positive counter of L (or starts a new counter at 1 in Q). Repeat q times. At b=4 the last rule instead leaves the two leading zeros and defers the incremented counter. At b=3 the last rule and a=0 rule produce the right count c+2, following count d+2, and a single leading zero on L. At b=2 use the sixth rule. If the active counter q>=2, the right leading count is q, with one leading zero on L. At a positive right leading count >=2 and left of form (0,s,0,...), the second and first rules compose to prepend s+1 to R and remove the pair (0,s) from L; at empty left prepend the marker 1. This flushes all deferred output and returns to P. The small q cases from P have empty deferred stack and follow directly from the first/sixth rules.

This is a deterministic *streaming rewrite* of the right list: on a residue-1 count b=3q+4 emit q+2, consume the count, and add carry 2q+2 to the next count (zero if absent). Continue until the residue-0 or residue-2 terminal clause emits its finite prefix and copies the remaining suffix. The only sufficient-normal-form obstruction is entering Q with b<8. Proving its absence on the seed [2] would give the complete nonhalting proof for all 25 F0 completions. The guard is deliberately stronger than actual safety, so a counterexample to the guard is not by itself a terminal query. For instance prepared P right list [4] reaches Q b=2 and may halt; arbitrary prepared states are not safe.

For a residue-1 input b=3q+4, the next Q guard is exactly c+2q>=6, or 2b+3c>=26. The finite list of dangerous prefix patterns is b=4 with c=0,2,3,4,5; b=7 with c=0,2,3; b=10 with c=0. Every other residue-1 positive list passes the next guard. This focuses the proof on actual reachability of small prefixes, rather than unstructured primitive scanning.

## Experimental status

A JavaScript implementation of the seven exact B0 rules completed 2,000,000 selected returns from the blank seed without reaching F0; among Q-shaped B0 states the minimum second run was 8. A separate normalized P/Q/U evaluator completed 5,000,000 transfer/flush operations without encountering a Q count <=5 or the unsafe top-one/deeper-stack case. These are finite observations, **not** an inductive proof of the stronger Q>=8 guard. Uncorrelated finite capped-count stack abstractions admitted spurious guard violations; ordinary finite-factor languages at caps 8–24 and factor widths 2–4 also admitted violations. A useful next step is to exploit the exact carry/output correlation of the deferred transducer to construct a regular or arithmetic invariant of its *whole-list* returns, or an exact backward obstruction analysis. Do not claim any new Cover from these observations.
