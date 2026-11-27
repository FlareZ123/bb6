# Raw42/0RA exceptional leaf 1659: finite-state return transducer

Table `1RB1RE_1RC0RA_0RD---_1LD0LB_1LF0RC_0LA0LF`, sole hole C1. This gives an exact *conditional* return grammar for the outstanding exceptional leaf. It reduces its nonhalting question to an inductive language for a small subsequential word transducer. The macro derivation and conditional nonhalting bridge are locally kernel-checked against original SweepPumping dependencies in [Raw42Leaf1659.lean](Raw42Leaf1659.lean), Lean 4.36.0-rc2, with only propext and Quot.sound. The source SHA256 is a3a051f600e6e770dbb452104049ac04bb8e327e5872b9adc0587ddc0129e1f2. No leaf decision or parent Cover is asserted.

## Return words and literal transitions

Write A[w] for state A, scanned cell at the first bit of w, blank left tape, w followed by implicit zeros. The blank trajectory reaches A[000101] after 17 live steps. All successful macro returns below shift the head exactly two cells left. The sufficient input form is `0001v`. Reading the first four cells takes six steps and reaches D immediately to their right, with processed left word `1110`.

At the right frontier in D, let its left word (in spatial order) be P followed by an active run of a≥3 ones and a zero. P is either empty or begins with a one and consists of positive one-runs separated by single zeros, ending in zero. The unprocessed suffix is arbitrary.
* Every frontier 1 is consumed in three primitive steps: D1→B0→C0→D; it replaces the last zero and frontier one by 10. Thus k consecutive ones increment the active run by k, preserving the right frontier form.
* The next frontier 0 causes a seven-step return to the frontier, now in E, with processed word P followed by 1^(a+k−2)0101. All one-runs remain positive.
* E0 starts the left return sweep. It writes one and enters F, which clears the last one-run, then crosses the preceding zero and reaches A on the preceding run. A1→E0 starts the same operation for that run. By induction over positive runs separated by one zero, all processed ones are cleared and each separator is changed to one; the final F0 on the blank cell at the left of the processed word moves to A one further left. Thus the new word is 00 followed by the bitwise complement of the processed word and of the consumed E0, then the untouched suffix. No C1 query occurs.
* E1 writes zero and moves to C, which must read zero. The processed word is now P followed by 1^(a+k−2)010100. The next D0 consumes a zero and in 15 steps merges the two trailing one-runs into a new active run of length five. The next D1 instead creates one further length-one run separated by a zero. The following D0 merges that trailing run into the preceding one, producing an active run of length four. The following D1 increments the trailing run; a third consecutive D1 yields active length three. A zero when the length is two is outside this sufficient grammar. These rules preserve the arbitrary unprocessed suffix.

Equivalently, in an active state A_a (a in {3,4,5}), consume k ones then zero, emit 0^(a+k−2)1, and enter parser state E. Initially consume 0001 and emit 00, then enter A_3. From E:
| Input | Emit | Next |
| --- | --- | --- |
| 0 | 0101 | copy all remaining bits |
| 100 | empty | A_5 |
| 1010 | 01 | A_4 |
| 10111 | 0101 | A_3 |

The E1/C1 and intermediate active-length-two cases are deliberately outside the sufficient grammar. All successful parses on finite words with implicit zeros eventually terminate in the copy state: the forward frontier consumes input monotonically, and any unfinished valid parser reaching the all-zero suffix either terminates or enters an active state and then terminates. Every successful parse gives a positive-time literal-machine return avoiding C1; an infinite orbit of successful parses from the authentic seed would prove nonhalting for every completion.

## Evidence and next edge

The Python reference transducer in `trans42.py` reproduces 10,000 accelerated returns from the seed, ending with a 20,041-bit word. Its first 100 returns independently match primitive replay . This is finite evidence, not an invariant. A k-gram factor abstraction through k=26, and the forward transition-subgraph abstraction on the minimized domains of the first 400 iterates, failed to close. The domain DFA sizes grow slowly (11 at depth 1, 383 at depth 100, 532 at depth 400), so simple finite-domain iteration did not stabilize. Seek a stronger inductive regular language (e.g. ICE/SMT synthesis using the finite parser) or a structured word invariant; do not merely extend the orbit replay. The formal theorem `never_of_language` reduces the remaining proof to an inductive language of authentic return tails. The arbitrary-tail frontier and left sweep are already proved. No global roster change.
