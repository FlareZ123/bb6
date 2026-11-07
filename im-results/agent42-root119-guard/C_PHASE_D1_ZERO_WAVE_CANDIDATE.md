# C-phase D1 zero-wave return candidate

Date: 2026-11-07  
Status: strong finite computational evidence; general Lean proof not yet complete.

## Proposed theorem

Let \(b=(B,h,t)\) be a reached B/0 configuration. Suppose \(r\ge2\) and

\[
t(h-1-i)=1\quad(0\le i<r),\qquad
t(h-r-1)=0,\qquad
t(h-r-2)=1.
\]

Then the observed return law is

\[
\operatorname{run}(r+7,b)=\operatorname{some}(b')
\]

where \(b'\) is B/0 with head \(h-r+1\). The returned head cell is zero because it is one of the \(r\) cells erased by the C/1 scan when \(r\ge2\).

## Transition derivation

The run decomposes into:

1. B/0 writes one at \(h\) and moves left to C at \(h-1\).
2. C/1 erases the \(r\) consecutive ones at \(h-1,\ldots,h-r\).
3. C/0 at \(h-r-1\) writes one and moves left to D at \(h-r-2\).
4. D/1 writes one and moves right to F at \(h-r-1\).
5. F/1 writes zero and moves right to D at \(h-r\).
6. D/0 writes zero and moves left to E at \(h-r-1\).
7. E/0 writes one and moves right to A at \(h-r\).
8. A/0 writes one and moves right to B at \(h-r+1\).

The total is \(1+(r+1)+5=r+7\) steps. The final head is \(h-r+1\).

The resulting four-cell suffix from \(h'-3\) through \(h'\), where \(h'=h-r+1\), is \(1110\). All writes occur at or to the right of \(h'-3\). This gives a plausible direct proof that the macro preserves NoLeft4: every affected four-cell window ending at or to the left of \(h'\) either lies in the unchanged prefix or has a final one among its last two cells. The shield argument still needs a formal Lean proof.

## Ten-million-step evidence

The updated Node.js audit file test-root119-two-wave-census.cjs checks both the predicted return time and returned head for every recognized interval. It reports 22,984 B/0 configurations and 22,983 consecutive intervals:

| Class | Count |
|---|---:|
| C-phase D1 candidate | 15,198 |
| Existing odd-wave | 7,508 |
| Existing left-one-wave | 177 |
| New even prefix theorem | 21 |
| New odd-even prefix theorem | 22 |
| Unmatched left-prefix candidates | 8 |
| Other | 49 |
| **Total** | **22,983** |

The C-phase candidate run-length histogram is:

- \(r=2\): 1 interval;
- \(r=3\): 15,176 intervals;
- \(r=4\): 21 intervals.

The previous ten-step class is exactly the \(r=3\) subfamily. The \(r=2\) and \(r=4\) cases add 22 intervals. The Node replay passes all assertions, including the full class-count vector, run-length histogram, predicted return times, and returned heads.

## Proof status and next steps

A first standalone Lean 4.36.0-rc2 model attempt was started but remains incomplete. Its errors are proof-engineering issues around cast normalization, induction hypotheses for the recursive C scan, and composition of run; no counterexample to the transition derivation was found. Do not treat this candidate as formally proved.

Next:
1. Prove a recursive C-scan lemma that erases \(r\) ones and exits through C/0 into D at \(h-r-2\).
2. Prove the five-step D/1-to-B/0 tail with exact tape.
3. Compose the exact run lengths to obtain \(r+7\).
4. Prove NoLeft4 preservation using the unchanged prefix and the final \(1110\) suffix.
5. Add a source-import CI gate and rerun the 10-million-step audit.

This is an intermediate research candidate, not an exact BB(6) result or a universal upper bound.
