# Finite synchronizing-word scan for the #623 root cocycle

**Status:** computational observation only; not an all-time theorem.

## Definition

For a canonical root state (D(a,d)), write
- (q=\min(a,d)),
- (p=|a-d|),
- (g=p-3q),
- (x=2g-\gamma_s), with \(\gamma_{LO}=18,\gamma_{LE}=10,\gamma_{RO}=2,\gamma_{RE}=4\),
- (y=6q).

Let \(\ell\) be the least integer with \((3^\ell-1)/2\ge q+3\), and put
\[
B=\max(34\ell+140,36\ell+88).
\]
Choose the least \(k,j\) such that \(3^k>B\) and \(3^j>B^3\). Define the digit-pair word
\[
W(a,d)=((x_i,y_i))_{i=k+1}^{j-3},
\]
where \(x_i,y_i\) are the base-three digits of \(x\bmod 3^j\) and \(y\bmod 3^j\).

For each branch, use the carry transducer:
\[
\begin{array}{ll}
L:&r_x=x_i-y_{i-1}+a_i,\quad r_y=y_{i-1}+b_i,\\
R:&r_x=-x_i-x_{i-1}-y_{i-1}+a_i,\quad r_y=x_{i-1}+y_{i-1}+b_i.
\end{array}
\]
The output digits are the residues modulo 3 and the next carries are the floor quotients by 3.

The scan quantifies over **all nine possible previous digit pairs** \((x_{k},y_{k})\), and all admissible initial carries:
- L: \(a_k,b_k\in[-2,2]\), giving 225 initial transducer states;
- R: \(a_k\in[-4,1]\), \(b_k\in[-2,2]\), giving 270 initial transducer states.

A word is called *synchronizing here* if, for each branch separately:
1. every initial state produces an x-output word that is neither all 0 nor all 2;
2. all initial states finish with the same carry pair (the final previous digit pair is automatically the word's final symbol).

## Reproduction and observed result

Run:

```bash
node synchronizing_word_scan.js 10000
```

Observed output with Node.js BigInt arithmetic:

- 9,968 root states scanned, indices 33 through 10,000 inclusive;
- the index-16 anchor is \(D(876,235)\), matching the repository's established checkpoint;
- word lengths range from 8 to 17;
- zero failures for the left transducer;
- zero failures for the right transducer.

Thus the finite run checks
\[
9968\times(225+270)=4,934,160
\]
carry trajectories. For every scanned root state, both branch transducers map all admissible initial previous-digit/carry states to a single final carry pair, while producing a nonmonochromatic x-output word.

## Why this may matter

This is stronger than checking nonmonochromatic output for the actual low-digit boundary: the previous digit pair is universally quantified, and the final carry synchronizes. The word is a reset word for each of the two finite carry automata, over the scanned root states.

The lower endpoint is \(k+1\), still above the terminal width because \(3^k>B\) and the terminal strip is narrower than \(B\). The upper endpoint remains below \(j\), with \(3^j>B^3\). Therefore the nonmonochromatic output is relevant to the terminal-strip exclusion.

## Limitations and next step

This does **not** prove that every future root word is synchronizing. A direct attempt to show that every output word of a synchronizing input word is itself synchronizing has counterexamples when arbitrary output carries are allowed. The next task is to identify an additional invariant on the actual boundary carry / output prefix, or prove a finite-state closure theorem for the authentic root transition.

The high-level recurrence is transcribed from Agent8's root replay script. The anchor check is useful but is not a formal proof of the recurrence. The scan is diagnostic evidence, not a replacement for the source-compiled Lean developments.

Related files:
- Agent41 integer carry transducer: im-results/agent41-623-integer-carry-transducer/README.md
- Agent8 root replay: im-results/agent8-623-inverse/root_mass_corridor_survey.js
- Signed coordinate normal form: SignedCoordinateNormalForm.md


## Short reset-subword certificates

A second pass checks every contiguous subword of lengths 3 through 6 and asks whether that subword itself synchronizes both branch automata (with the same universal previous-digit and carry quantification). The checker is in synchronizing_reset_subwords.cpp.

Reproduce both stages with:

```bash
g++ -O3 -std=c++17 synchronizing_reset_subwords.cpp -o /tmp/reset-subwords
node synchronizing_word_scan.js 10000 --emit-blocks | /tmp/reset-subwords
```

Observed over the 9,375 available exported blocks (indices 33 through 9,407 in the captured export):

| Minimum common reset-subword length | Number of blocks |
|---:|---:|
| 3 | 9,036 |
| 4 | 337 |
| 5 | 1 |
| 6 | 1 |

The length-5 exception is index 3,874; the length-6 exception is index 237. There are no blocks without a common reset subword of length at most 6.

This is a local-certificate strengthening of the full-word synchronization scan. It still remains a finite computational observation: the subword language has not yet been proved invariant under the authentic root transition.
