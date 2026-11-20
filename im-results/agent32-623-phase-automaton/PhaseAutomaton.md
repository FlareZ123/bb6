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
x'=x-3y+C_L,quad y'=y+F_L
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
