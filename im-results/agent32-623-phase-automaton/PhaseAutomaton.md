# Buffered finite-state phase induction for the #623 root

**Status:** a proof architecture for the authentic (D(0,7)) orbit, not a theorem. It is intended to replace finite replay extension with a finite automaton closure test. Keep in `im-results/`.

## 1. The central word and its exact moving-window update

Use the signed coordinates
[
x=2g-gamma_s,qquad y=6q,
]
where (q=min(a,d)), (g=|a-d|-3q), and
(gamma_s=(18,10,2,4)) in LO/LE/RO/RE.

Let
[
B(ell)=max(34ell+122,36ell+88),quad
3^{k}>B(ell),quad 3^{j}>B(ell)^3
]
with (k,j) least. The source-faithful diagnostic uses the digit-pair word
[
W_n=((x_i,y_i))_{i=k_n+1}^{j_n-3}.
]
The finite scan checks that (W_n) synchronizes both branch transducers over the *full* carry rectangles.

Agent 41's mass-indexed depth lemma gives
[
k_{n+1}-k_nin{0,1},qquad
j_{n+1}-j_nin{0,1,2,3}.
]
If (U_n) is the output digit-pair word produced from (W_n) by the actual current branch, then the next word has the exact sliding-window form
[
W_{n+1}
=
operatorname{drop}_{delta_n}(U_n)
mathbin{|}operatorname{append}_{eta_n}(U_n^{m high}),
]
where (delta_n=k_{n+1}-k_nin{0,1}), (eta_n=j_{n+1}-j_nin{0,1,2,3}), and (U_n^{m high}) is generated from at most three extra input digit pairs at positions (j_n-2,j_n-1,j_n). Thus only a one-symbol low shift and a three-symbol high lookahead are needed for the *full* word. The terminal middle subword beginning at (k_{n+1}+2) drops one additional low symbol, so its overlap with the old output begins at (k_n+3).

## 2. Exact finite checker automata

For each branch (bin{L,R}), define a deterministic digit transducer with state
[
(x_{m prev},y_{m prev},a,b)
]
and input alphabet ({0,1,2}^2). Its transition and output are the exact formulas in `synchronizing_word_scan.js`:
- L: (r_x=x_i-y_{i-1}+a_i), (r_y=y_{i-1}+b_i);
- R: (r_x=-x_i-x_{i-1}-y_{i-1}+a_i), (r_y=x_{i-1}+y_{i-1}+b_i).
The output digits are the residues modulo 3 and the new carries are floor quotients by 3.

Use the full start rectangles:
- L: previous digit pair arbitrary, (a,bin[-2,2]);
- R: previous digit pair arbitrary, (ain[-4,1]), (bin[-2,2]).

The smaller ([-1,1]^2) rectangle is invalid: the authentic index-38 R-x carry is (-2).

A word is (b)-synchronizing if every admissible start:
1. remains in the branch's carry rectangle;
2. emits an x-output word containing a digit different from 0 and a digit different from 2;
3. ends in the same complete transducer state.

The conjunction for L and R is a regular language over the nine-symbol digit-pair alphabet. It can be recognized by the finite product of the two all-start checker automata. This is stronger than merely having one reset subword.

## 3. The phase that must be carried

A closure proof cannot treat the output word as an arbitrary string or the next carry as arbitrary. It should track the finite boundary phase:

- the actual current branch and sector;
- the actual previous digit pair and full initial carry at (k_n+1);
- the one low digit pair needed when (k) shifts;
- the three high input digit pairs at (j_n-2,j_n-1,j_n);
- the two possible low-shift cases and four possible high-shift cases;
- the finite checker-automaton transformations for (W_n), and for the suffixes needed after dropping 0 or 1 low symbols;
- the exact output carry/previous-pair phase at the end of (W_n).

The actual start phase is needed for the first output symbols. A reset subword, when it occurs, makes the later output suffix independent of the initial phase. The finite scan reports full-range common reset subwords of length 3--6, with earliest end at most 13 over the scanned root states; this is diagnostic evidence only. The invalid small-start reset scan must not be used.

The high-end lookahead and low-end shift are bounded, so the transition from one checker phase to the next is finite-state. A product automaton can process (W_n), generate (U_n), trim the allowed low prefix, append the bounded high tail, and compute the next pair of checker states without storing the unbounded word itself.

## 4. Exact arithmetic interfaces

The root affine update is source-shaped:
[
x'=x-3y+C_L,quad y'=3y+F_L
]
on L, and
[
x'=-4x-3y+C_R,quad y'=3x+3y+F_R
]
on R. The correction-only bound is not the total carry bound; use the full rectangles above.

The three-state drain transducer gives the exact statistics
[
N=(2b-1+3^L)/4,quad
R=#{	ext{nonzero ternary digits of }N},quad
E=#{	ext{2-digits of }N},quad
D=L-2E.
]
These statistics determine the exact correction terms and branch threshold. They are not a substitute for the root phase.

The conditional reduction in [BranchSelection.md](BranchSelection.md) shows that, once the central word excludes the terminal window, the exact output-side test (gge T) reduces to (g>0). This can simplify the branch component of the phase graph, but the implication is conditional on the very terminal-window invariant being proved.

## 5. Acceptance test and falsification discipline

The first computational task is **not** another root replay. Build the finite product-state transition relation and ask whether the proposed buffered checker invariant is closed under every source-permitted phase transition.

- If BFS finds a counterexample, preserve the shortest phase witness, identify the exact source branch and boundary carry, and revise or abandon the invariant.
- If it closes, export the reachable finite phase graph and a machine-checkable transition certificate. Then formalize the finite closure and its source prefix against the unchanged pinned machine definitions.
- Do not infer closure from the 20,000-state replay, the observed eight sector edges, or the reset-word frequency table.

The existing 20k source-faithful replays are enough for debugging and prefix discovery. The proof target is a finite phase-graph closure theorem plus the exact source terminal-window bridge. A #623 decision would still classify only this difficult machine/cylinder, not by itself establish the universal BB(6) upper bound.


## 6. A smaller reset-pattern automaton

A more economical checker may use the finite pattern set
[
mathcal P={win({0,1,2}^2)^r:3le rle6, w
	ext{ synchronizes both full-range branch transducers}}.
]
Here “synchronizes” includes all three conditions in Section 2: every start remains in range, every trajectory's x-output is nonmonochromatic (not all 0 and not all 2), and all final states coincide.

If a word contains some (w\in\mathcal P) as a contiguous subword, then the *whole word* is synchronizing for both branches: before the reset subword, every trajectory is still in the admissible carry rectangle; the reset subword sends every possible previous-digit/carry state to the same state and has already set both nonmonochromatic output flags; the suffix preserves state equality and the flags. This explains why the common-reset-subword diagnostic is a sufficient certificate for the full-word synchronization property.

The language of words containing a member of the finite set (mathcal P) is regular and can be recognized by an Aho--Corasick-style finite automaton. The phase-closure task can therefore be reduced to a product of:
1. the exact current-branch digit-pair transducer;
2. the reset-pattern recognizer for (mathcal P);
3. the one-low-symbol / three-high-symbol sliding-window phase;
4. the actual full-range boundary carry and sector phase.

The existing full-range diagnostic found a common pattern of length 3--6 in every one of the 9,968 words checked, with earliest end at most 13. This does not establish that (mathcal P) is preserved by the authentic root update. In particular, a reset pattern in the old word need not survive in the old output suffix; the recognizer must process the *entire next window*, including its bounded high-end extension. The counterexample at root index 33 to naive reset-suffix closure remains a regression test.

This pattern-language route is preferable to retaining the full transformation monoid of every checker state, provided the finite set (mathcal P) can be enumerated and minimized without losing the universal start-state quantifiers.


The reset-pattern trie is not the final automaton size. The exact generated Aho--Corasick recognizer has 34,916 trie states, but Moore minimization of its complete absorbing-acceptance DFA gives **263 states**, with partition counts (9,102,159,234,263,263). The minimized transition table is stored in [ResetPatternDFA.json](ResetPatternDFA.json). Its acceptance behavior was checked against direct substring membership for every digit-pair word of lengths 0 through 6 (597,871 words). This is a finite automaton identity, not an orbit-closure theorem.


## 7. Post-reset phase collapse

The exact pattern enumeration gives another useful compression. Immediately after any minimal common reset pattern (length 3--6), the final previous digit pair ranges over all 9 possibilities, but the carry pair is restricted to:
- L: ((a,b)\in\{(-1,0),(0,0)\}), so 18 complete post-reset states;
- R: ((a,b)\in\{(-3,1),(-2,0),(-2,1),(-1,0)\}), so 36 complete post-reset states.

For each branch, every one of the 9 final digit pairs occurs with every listed carry pair. This is an exact enumeration over all 29,445 minimal reset patterns and follows from the same all-start synchronization check. The state IDs are in `ResetPatternDFA.json`.

This means the *unbounded suffix after the first reset* can be processed from at most 18 L or 36 R transducer phases, rather than 225 or 270. Composing those with the 263-state reset recognizer gives at most 4,734 L or 9,468 R post-reset product states before adding the small window-shift phase. The prefix before the first reset remains a bounded phase (the existing diagnostic has reset end at most 13); its output effect can be summarized by the 263-state checker. This is the main compression to exploit in the next closure computation.


## 8. The bounded-prefix induction target

The useful root invariant is not “the entire word is reset”; it is the bounded-prefix property
[
\mathsf{Reset}_{13}(W)
\quad\Longleftrightarrow\quad
\text{the 263-state DFA accepts the first }\min(13,|W|)\text{ symbols of }W.
]
The existing full-range root diagnostic has this property at every scanned state: the first common reset pattern ends by position 13. The root word lengths in that diagnostic range from 8 to 17.

To prove induction, compose the actual branch transducer with two copies of the 263-state DFA:
- an input checker, which recognizes (mathsf{Reset}_{13}(W_n));
- an output checker, which reads the next-window word after the exact low shift (delta\in\{0,1\}).

Once the input checker sees a common reset pattern, the transducer state has collapsed to one of the 18 L or 36 R post-reset states from Section 7. Only the first 13 output symbols matter for (mathsf{Reset}_{13}(W_{n+1})). Thus the unbounded suffix is unnecessary: after the first reset, at most (13-p+\delta) more input symbols are needed, where (p\le13) is the reset end position. If the next word is shorter than 13, include its actual bounded high extension (at most three symbols); saturate the word-length phase at 14 so the one-symbol low shift is handled exactly.

The resulting product-state closure problem has finite components:
- pre-reset full carry state and the input/output DFA states;
- post-reset carry state from the 18/36 sets and the output DFA state;
- a prefix-position counter capped at 13/14;
- low-shift bit and high-extension count (0--3);
- sector/branch phase.

First test the strongest useful closure statement (all full-range start phases and all allowed shifts). If it fails, preserve the shortest counterexample and restrict only with source-derived root-phase constraints. If it closes, the finite reachable phase graph is the proof certificate. The index-33 output-suffix counterexample must remain in the test suite: closure is for the *whole next window*, not an arbitrary suffix.


## 9. Sector transition once the central-block bridge is available

The source parity table is:
- LO input gives odd output second counter;
- LE input gives even;
- RO input gives even;
- RE input gives odd.

By the conditional branch-selection lemma, output orientation is left iff (g>0). Combining orientation with parity gives the exact sector transition table outside the terminal window:

| Current sector | (g>0) (left output) | (g<0) (right output) |
|---|---|---|
| LO | LO | RO |
| LE | LE | RE |
| RO | LE | RE |
| RE | LO | RO |

Thus the sector phase is only a four-state component; the output-side decision is the sign bit of (g), and the parity update is fixed by the current sector. This recovers the eight possible sector edges without a drain-statistic comparison. It does not determine the next sign (g'); that remains part of the joint root phase and the digit transducer.
