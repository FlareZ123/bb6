# raw139 C1=0LA: complete four-hole candidate

Parent in A0,A1,...,F0,F1 order:
`[7,24,11,24,14,0,3,16,12,11,24,24]`.
Ordinary codes are 4q+2w+d (d=1 right); 24 is unassigned.

## Unbounded carry closure (leaf 86)

The partial table `[7,21,11,24,14,0,3,16,12,11,3,7]` has one unassigned slot B1. Define a section with E state, head-inclusive reversed left list 1, and right list
`000 (100)^n 000000 1 R`.
The blank computation enters it at move 94 with n=1 and R=1.

The tail language consists of three terminal words 1, 0000111, 110111, and arbitrary iterated prefixes T=001, W0=000000001, W1=11000001, W2=0000110001, W3=110110001. The exact F scanner with initial left token 0011 and arbitrary left suffix L runs to E with left suffix L and right 01 followed by a new tail. Its structural rewrite is:

- 1 -> 0000111;
- 0000111 -> T 110111;
- 110111 -> W0 1;
- T R -> T transform(R);
- W0 R -> T W1 R;
- W1 R -> W2 R;
- W2 R -> T W3 R;
- W3 R -> W0 transform(R).

The recursive branches take 5+k+5 and 13+k+11 moves respectively; the direct base cases take 20,16,26,16,16,16. All one-block steps are literal symbolic reductions over arbitrary untouched tails. Four E returns advance n to n+2, preserving the language. This proves unbounded live prefixes without visiting B1, hence all 25 compatible completions are nonhalting when the source bridge is accepted.

`C1ZeroLACarry86.lean` proves the uniform existential scanner cost (independent of L), section advance, entry and progress by induction. Local Lean 4.36.0-rc2 checked these against the exact copied computational definitions and core lemma proofs, with [propext, Quot.sound] and Classical.choice for next_sound. The imported original-machine bridge uses the already established never_of_growth. Full-source acceptance is pending the manual zero_la_only audit.

## Exhaustive parent assembly

`generate_c1_zero_la.py` uses the shared exact first-hole search and FAR witness synthesis from `generate_c1_one_lc.py`. It deterministically finds:

| Leaf or node type | Count |
|---|---:|
| Internal first-hole splits | 85 |
| Side-cycle leaves | 1252 |
| Last-hole leaves | 546 |
| FAR leaves | 136 |
| Symbolic nonhalting leaves | 22 |

Of the symbolic leaves, 13 are in C1ZeroLAFour / C1ZeroLAVars (original-source accepted run 45582686349), eight in C1ZeroLASweeps (pending), and the final one is the new carry closure above. The last-hole candidate 88 reaches B1 at ordinary step 260. The final delayed side cycle, candidate 94 (table [7,21,11,13,14,0,3,16,12,11,5,24]), starts at step 2075 with head 41, ends after 10 moves at head 43, and has leftmost visited coordinate 39. State, entire right ray (bits 11), and relevant left two cells agree under translation. These are untrusted numerical witnesses; generated Lean calls the original checking lemmas.

The candidate weighted bound is 266, covering all 25^4 = 390625 completions if the original-source CI succeeds. No whole raw139 cover or BB(6) upper bound follows yet. Generate C1ZeroLAParent.lean before importing it. The current manual workflow agent6-early-siblings.yml zero_la_only compiles the entire parent dependency closure and checks standard axiom profiles.
