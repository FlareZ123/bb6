# Source-drain summary to finite-state transducer: proof sketch

**Status:** a new proof route for the missing source/finite-state interface. The identities below are derived from the existing definitions and independently checked by a JavaScript translation; they are not yet Lean theorems. This note is an intermediate result, not a certified #623 closure.

Relevant definitions:
- `sourceDrainStep`, `sourceDrainSummary`, and `drainB_digit_cocycle` in [DrainDigitSourceBridge.lean](agent1-machine623-3euclidean-correction-bounds/DrainDigitSourceBridge.lean).
- `step`, `run`, and `runStats` in [DrainDigitTransducerCarry.lean](agent1-machine623-3euclidean-correction-bounds/DrainDigitTransducerCarry.lean).

## 1. Two transducer offset identities

Let `run n b s` read the lowest (n) base-three digits of (b), starting in state (s\in\{A,B,C\}), and return the emitted output integer together with the final state. The transition table gives the following output identities for every (n,q\ge0):

[
\operatorname{out}(\operatorname{run}(n,q+1,B))
=
\operatorname{out}(\operatorname{run}(n,q,A)),
\]
[
\operatorname{out}(\operatorname{run}(n,q+1,A))
=
\operatorname{out}(\operatorname{run}(n,q,C)).
\]

These are a mutually inductive pair on (n). Split (q=3t+r):

| Identity | (r) | First transition on left | First transition on right | Tail identity |
|---|---:|---|---|---|
| B-shift | 0 | B/1 emits 2, next B | A/0 emits 2, next B | B-shift at (t) |
| B-shift | 1 | B/2 emits 1, next A | A/1 emits 1, next A | A-shift at (t) |
| B-shift | 2 | B/0 emits 0, next A, quotient (t+1) | A/2 emits 0, next C, quotient (t) | A-shift at (t) |
| A-shift | 0 | A/1 emits 1, next A | C/0 emits 1, next A | A-shift at (t) |
| A-shift | 1 | A/2 emits 0, next C | C/1 emits 0, next C | A-shift at (t) |
| A-shift | 2 | A/0 emits 2, next B, quotient (t+1) | C/2 emits 2, next A, quotient (t) | B-shift at (t) |

The identities claim equality of emitted output words only, not final-state equality. Final states can differ even at n=1: for q=2, B on q+1=3 emits 0 and finishes in A, while A on q=2 emits 0 and finishes in C; the A/C shift emits 2 on both sides but finishes in B versus A. The source-summary bridge therefore identifies weighted output counts only; the terminal phase must remain a separate component of the S-window product. The count-only version for `runStats` follows by the identical case split, adding the same first output digit and applying the paired tail identity.

## 2. The source-drain block is exactly one nonzero output

For a positive source drain parameter (B), put (k=B-1), and let
[
(v,q,\epsilon)=\texttt{sourceDrainStep}(k).
]
The defining specification is
[
k=\operatorname{ternaryOnes}(v)+3^v(3q+2\epsilon),
\qquad \epsilon\in\{0,1\}.
]

If (v\ge1), the lowest (v+1) ternary digits of (B=k+1), low to high, are
[
2,\underbrace{1,\ldots,1}_{v-1\text{ copies}},2\epsilon,
]
and the remaining high quotient is (q). Starting from A, the transducer emits
[
\underbrace{0,\ldots,0}_{v\text{ copies}},
\begin{cases}1&\epsilon=0,\\2&\epsilon=1,\end{cases}
]
and returns to A. Thus this block has length (v+1), exactly one nonzero output, and exactly (epsilon) output-2 digits.

If (v=0), the decomposition is (B=1+2\epsilon+3q):
- (epsilon=0): the first input digit is 1; A emits 1 and returns to A, then the tail is (q) from A.
- (epsilon=1): the first input digit is 0; A emits 2 and moves to B, and the tail is (q+1) from B. The B-shift identity replaces that tail output by the output of (q) from A.

So in every case the first source-drain block contributes exactly
[
(\text{length},\text{twos},\text{nonzero outputs})=(v+1,\epsilon,1),
]
followed by the ordinary A-start transducer output for (q).

## 3. The missing source/finite-state theorem

The source recursion is
[
\texttt{sourceDrainSummary}(B)
=(v+1+L(q),\epsilon+E(q),1+R(q)),
]
where ((L(q),E(q),R(q))=\texttt{sourceDrainSummary}(q)). The block decomposition above therefore gives, by strong induction on (B), the exact target theorem
[
\boxed{
\begin{aligned}
(\texttt{runStats}(L,B,A)).\texttt{twos}
  &=\texttt{sourceDrainTwos}(B),\\
(\texttt{runStats}(L,B,A)).\texttt{ones}
 +(\texttt{runStats}(L,B,A)).\texttt{twos}
  &=\texttt{sourceDrainCalls}(B),
\end{aligned}
\qquad L=\texttt{sourceDrainLength}(B).
}
]
No extra RE evaluator offset should be added: use the exact (B) passed to `drainB`; `sourceDrainSummary` mirrors the actual `drainB` recursion, including the bundled right-even convention already documented in `drainB_digit_cocycle`.

Combining this theorem with the existing
`drainB_digit_cocycle` yields the actual source identities with the finite-state weights:
[
aa+L=a+2E,\
2aa+dd=2a+d+3B+2R,
]
where (E=\texttt{runStats.twos}) and (R=\texttt{runStats.ones}+\texttt{runStats.twos}). This is precisely the missing identification needed for the source `corrC/corrF) interface to consume the transducer weights rather than an unconnected digit statistic.

A companion length lemma should prove, for (B\ge1),
[
L\equiv B\pmod2,\qquad
3^{L-1}\le2B-1<3^{L+1}.
]
Then `drain_transducer_exact_canonical` supplies the exact output integer
(4N=2B-1+3^L) for the same source-drain length.

## 4. Independent finite checks

A dependency-free JavaScript translation of the two recursive definitions and the nine-entry transducer table found:

- (B=0,1,\ldots,100000): zero mismatches in (E=\text{twos}), (R=\text{ones} + \text{twos}), parity, either canonical length inequality, or (4N=2B-1+3^L).
- Offset identities: zero output-word mismatches for (n=0,\ldots,8) and (q=0,\ldots,9999). Final-state equality is not claimed; for example, at n=1,q=2 the B-shift output words agree but the final states differ.

These are implementation checks, not proof. The induction above is the proposed Lean route. Keep this file in `im-results/` until the theorem is implemented, compiled against the exact imports, and its transitive axioms inspected.
