# Source-derived carry starts and a three-symbol reset

**Status:** exact conditional finite-state result. The full universal carry rectangles and their counterexamples remain preserved; this is a separate specialization justified by the arithmetic source-carry bounds.

## 1. Source-derived start rectangles

The source-carry formulas and correction bounds are recorded in `StartCarryRectangleInclusion.md`. Under its hypotheses `|C|, |F| ≤ B < K=3^k`, the quotient numerators give:

- L:
  `-4K+3 ≤ x_{k+1}-3y_k+C ≤ 4K-1`,
  `-K ≤ 3y_k+F ≤ 4K-3`.
  Hence `carryX ∈ [-2,1]`, `carryY ∈ [-1,1]`.
- R:
  `-10K+7 ≤ -x_{k+1}-3x_k-3y_k+C ≤ K`,
  `-K ≤ 3x_k+3y_k+F ≤ 7K-6`.
  Hence `carryX ∈ [-4,0]`, `carryY ∈ [-1,2]`.

All nine previous digit pairs remain possible in this abstraction. Thus the source-derived initial sets have 108 L states and 180 R states. The transducer transition spaces are **not** shrunk: the full 225-state L and 270-state R rectangles remain closed under every digit-pair transition. Only the set of admissible initial states is restricted by the source arithmetic.

## 2. A common three-symbol reset word

Encode a pair ((x,y)) by `3*x+y`. The word

`[1,0,0]` = **01 00 00**

is a common reset for every source-derived L and R start state. In both branches, it maps every allowed initial state to exactly

`(prevX, prevY, carryX, carryY) = (0,0,-1,0)`.

It also makes the emitted x-digit sequence nonmonochromatic (it contains neither only 0s nor only 2s).

### Direct derivation

For L, write the initial state as `(p_x,p_y,a,b)`, with `a∈[-2,1]`, `b∈[-1,1]`, and `p_x,p_y∈{0,1,2}`. On input 01, the next carries are

`a₁=floor((a-p_y)/3) ∈ [-2,0]`,
`b₁=floor((p_y+b)/3) ∈ [-1,1]`.

On the next input 00, the carries become

`a₂=floor((a₁-1)/3)=-1`,
`b₂=floor((1+b₁)/3)=0`.

The final 00 leaves them at `(-1,0)`, with previous pair `(0,0)`.

For R, the first 01 gives

`a₁=floor((a-p_x-p_y)/3) ∈ [-3,0]`,
`b₁=floor((p_x+p_y+b)/3) ∈ [-1,2]`.

The second 00 gives `a₂=floor((a₁-1)/3)∈[-2,-1]` and `b₂=floor((1+b₁)/3)∈[0,1]`. The final 00 therefore gives `floor(a₂/3)=-1` and `floor(b₂/3)=0`, again with previous pair `(0,0)`.

For nonmonochromaticity, the final L x-output digit is 2, while the second x-output digit can be 2 only when `a₁=0`; then `a-p_y∈[0,1]`, so the first x-output digit is not 2. For R, the final x-output digit is 1 or 2; if it is 2 and the second is also 2, then `a₁∈{0,-3}`. The case `a₁=-3` forces `a₂=-2`, making the final digit 1; the case `a₁=0` forces the first x-output digit to be 0. Hence the three x digits cannot all be 2. They cannot all be 0 because the final digit is nonzero.

The machine-readable artifact also checks the word against every one of the 108 and 180 start states. It records a full-L-rectangle counterexample: `(0,0,2,-2)` is outside the source-derived L rectangle and does not reset under this word. Thus the restriction is substantive, not a claim about the full universal rectangle.

## 3. Source-derived reset DFA and carry products

The reset-pattern search is rerun over exactly these 108 L and 180 R starts, retaining the full transition rectangles. As in the full-rectangle construction, it searches minimal common reset patterns of lengths 3 through 6 and builds/minimizes an Aho–Corasick recognizer.

| Quantity | Full-rectangle recognizer | Source-derived recognizer |
|---|---:|---:|
| Start states L + R | 495 | **288** |
| Minimal reset patterns, lengths 3–6 | 29,445 | **27,654** |
| Aho–Corasick states | 34,916 | **32,679** |
| Minimized reset DFA states | 263 | **252** |

The source-derived language contains the full-rectangle reset language. A finite product search over the two DFAs visited 543 state pairs, found no old-accepted/new-rejected word, and found the shortest new-only witness `01 00 00`.

Composing this 252-state recognizer with the full branch transducers, starting only from the source-derived states and both one-/two-symbol output skips, gives:

| Branch | Reachable product states | Product transitions | Minimal Moore states | Accepting product states |
|---|---:|---:|---:|---:|
| L | **1,818** | 16,362 | **635** | 18 |
| R | **2,604** | 23,436 | **813** | 36 |

The accepted product region is closed under all nine input symbols. The 18/36 accepting product states retain the post-reset transducer states; the minimized boolean Moore quotient collapses the accepting region to its accepting class.

The JSON artifact stores the 252-state DFA, product states, class maps, offset start classes, quotient outputs/transitions, and the language-inclusion witness. The builder and verifier reconstruct the arithmetic and check the quotient certificates.

## 4. Scope and obligations

This is a source-restricted one-window result, not an all-time root induction. Its validity for the authentic orbit depends on the source-carry inclusion hypotheses `|C|,|F|≤B<K` and the formulas in `StartCarryRectangleInclusion.md`. Agent49 should independently check that bridge before this specialization is used in a proof.

It does not show that every authentic root window contains a reset pattern, nor does it couple the next branch, sector, high-bit/drain state, low shift, and high-end extension. Agent32's whole-window phase product remains the induction task.

Do not replace or delete the full-rectangle automaton. The raw full-rectangle reset counterexamples, the six moving-window counterexamples, the index-33 whole-window suffix failure, and the phase/slack counterexamples remain mandatory adversarial regressions:
- `im-results/agent24-machine623-phase-slack-regressions.md`
- `im-results/agent32-623-phase-automaton/ClosureCounterexample.md`
- `im-results/agent32-623-phase-automaton/full_range_window_counterexamples.js`
- `im-results/agent32-623-phase-automaton/PhaseAutomaton.md`

Keep this result in `im-results/` until the source-carry bridge and whole-window induction are integrated.


## Reproduction

Run from the repository root:

```bash
node im-results/agent24-machine623-shifted-reset-product/build_source_derived_reset_product.js
node im-results/agent24-machine623-shifted-reset-product/build_source_derived_reset_product.js --verify
node im-results/agent24-machine623-shifted-reset-product/verify_source_derived_reset_product.js
```


## Lean verification

`SourceDerivedReset.lean` formalizes both branch reset lemmas and both source-carry quotient bounds. It compiles with Lean 4.36.0-rc2 using `import Lean` only (no Mathlib dependency):

```bash
lean im-results/agent24-machine623-shifted-reset-product/SourceDerivedReset.lean
```

The carry-bound theorems assume the residue intervals and `|C|,|F|≤B<K`; they do not derive the correction bounds from the drain transducer. The reset theorems then prove that the word `01 00 00` sends every state in the resulting L/R rectangles to `(0,0,-1,0)) and makes the emitted x digits nonmonochromatic.


## Kernel-checked source-to-reset implication

`SourceDerivedReset.lean` compiles with Lean 4.36.0-rc2 using `import Lean` only. Its combined theorems `left_source_derived_reset` and `right_source_derived_reset` compose the source-carry quotient bounds with the three-symbol reset proof. Under the explicit residue and correction hypotheses, they establish that `01 00 00` sends the corresponding L/R start to `(0,0,-1,0)) with nonmonochromatic emitted x digits.

The hypotheses `-B≤C,F≤B` and `B<K` are still inputs. The Lean file does not prove the drain-statistics machinery supplies those hypotheses; that is the remaining source-correction bridge.


## 5. Whole-target-window replay diagnostic

I replayed the exact `highLevelNext` root recurrence from `D(0,7)` through source indices 33–10000 and scanned each **entire target S-window** `[k'+2,j'-2)` with both reset DFAs. This is a finite diagnostic, not an all-time proof.

- Target windows checked: **9,968** (D34 through D10001).
- Full-rectangle 263-state DFA: **0** rejected windows; maximum first accepting position 12.
- Source-derived 252-state DFA: **0** rejected windows; maximum first accepting position 12.
- There were no windows accepted only by the source-derived DFA in this replay; the new-only language witness `01 00 00` is a valid extra reset word but was not needed to accept any of these finite target windows.
- At source index 33, the target D34 window has `x=57468`, `y=46704`, `S=67656`, `k'=6`, `j'=17`, length 7; both DFAs first accept after 4 symbols.

This does **not** remove the index-33 suffix-closure counterexample in `PhaseAutomaton.md`: that counterexample concerns assuming a reset in the old word survives in an arbitrary output suffix. The diagnostic above scans the whole next target window. The whole-window/extension requirement and the index-33 regression must remain.
