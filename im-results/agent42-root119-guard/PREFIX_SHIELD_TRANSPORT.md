# NoLeft4 transport through the even and odd-even prefix returns

Date: 2026-11-07  
Status: source-import verified in Lean 4.36.0-rc2; finite blank-root census corroboration; one synthetic counterexample identifies a necessary local guard for the odd-even theorem.

## Scope and invariant

All configurations and transitions are those of the auxiliary #119 machine imported from the repository's original Lean source modules. **NoLeft4 true true false c** means that no tape interval entirely to the left of the head of c has word **1100** in tape order:

\[
\forall x,\quad x+3<c.h\implies
\neg(c.tape(x)=1\land c.tape(x+1)=1\land
c.tape(x+2)=0\land c.tape(x+3)=0).
\]

The invariant excludes the repository's **BBad** stopping configuration, because every **BBad** witness contains such a left-of-head **1100** factor. This note concerns preservation across two already established conditional B/0 return families. It does not decide whether the blank-start orbit halts.

## Formal results

The source-import module is [Root119PrefixShield.lean](Root119PrefixShield.lean). It imports the exact machine and return definitions from [Root119OddEvenChain.lean](Root119OddEvenChain.lean), [Root119OddWaveRetreat.lean](Root119OddWaveRetreat.lean), and [Root119BShield.lean](Root119BShield.lean).

### Even prefix: unconditional shield transport

Assume a reached B/0 configuration b=(B,h,t) with

\[
t(h-1)=1,\quad t(h-2)=0,\quad t(h-3)=1,
\]
\[
t(h+1+j)=1\quad(0\le j<2n+1),
\]
\[
t(h+2n+2)=0,\quad t(h+2n+3)=0.
\]

The existing exact return theorem gives a reached B/0 after 2n+15 steps, with head h+2n+3. The new theorem

**b0_even_prefix_to_b0_preserves_NoLeft4**

adds the conclusion NoLeft4 true true false bout under the single input shield hypothesis NoLeft4 true true false b.

The proof isolates the nine-step B/0-to-F/1 prefix. Its resulting head is one cell to the left, and the newly exposed prefix cells end in 1. The following F/1 transition writes 0 with a preceding 1, so it cannot create 1100. The exact even D-sweep return is handled by a separate tape lemma: throughout the swept interval, every adjacent pair contains a 1. Windows strictly left of the sweep start are unchanged. This proves the endpoint shield for every natural sweep length.

### Odd-even prefix: shield transport with an explicit boundary condition

Assume the same three-cell left prefix, with

\[
t(h+1+j)=1\quad(0\le j<2n),
\]
\[
t(h+2n+1)=t(h+2n+2)=t(h+2n+3)=0.
\]

The exact return is after 6n+23 steps, with B/0 head h+2n+3.

The new theorem

**b0_odd_even_chain_to_b0_preserves_NoLeft4**

requires the additional hypothesis

\[
\neg\bigl(t(h-6)=1\land t(h-5)=1\land t(h-4)=0\bigr).
\]

The odd wave and the subsequent B/1 retreat move the head left while leaving the relevant exterior cells unchanged. The next F/1 transition is at head h-3 and writes 0. Its only newly exposed four-cell window is h-6,...,h-3. The extra condition rules out the first three bits 110, which are the only way that this newly exposed window could become 1100. After that step, the even-sweep shield lemma applies.

The boundary condition is a proof obligation with a concrete semantic role. It is not hidden inside a broad automation step.

The guard is sharp. The additional theorem **b0_odd_even_chain_to_b0_exact_bad_boundary** proves that whenever the three-cell boundary pattern is 110, the exact odd-even return produces a left-of-head 1100 and therefore fails NoLeft4. The proof tracks h-6 through h-4 unchanged through the odd wave and sweep, while the F/1 transition makes h-3 equal to 0. Combined with the preservation theorem, this gives an exact criterion: under the input NoLeft4 hypothesis and the odd-even return premises, the output is shielded precisely when the boundary guard holds.

## A formal synthetic obstruction to dropping the boundary condition

**oddEvenShieldCounterexample** is a B/0 configuration at head 0 whose tape is 1 exactly at positions

\[
-6,\ -5,\ -3,\ -1
\]

and 0 elsewhere. Lean proves **oddEvenShieldCounterexample_NoLeft4**: the input has no left-of-head 1100. Its right-side tape also satisfies the odd-even family assumptions at n=0: the required cells at positions 1, 2, and 3 are 0, and the three-cell left prefix is 101.

The boundary condition fails. The actual 23-step machine computation is checked by kernel reduction:

**oddEvenShieldCounterexample_run_summary**

It returns head 3 with cells (-6,-5,-4,-3)=(1,1,0,0). The theorem **oddEvenShieldCounterexample_run_not_NoLeft4** proves that the output is not shielded.

This is a synthetic configuration. No Reach proof is claimed for it. It establishes that NoLeft4 plus the displayed local prefix/right-corridor conditions alone do not imply odd-even shield preservation. A stronger theorem may still remove the extra guard if the blank-root reachability hypothesis implies it.

## Source and computational verification

The manual source-import workflow is [.github/workflows/agent42-root119-even-wave-prefix.yml](../../../.github/workflows/agent42-root119-even-wave-prefix.yml).

Successful source build: [CI run 42415186262](https://github.com/FlareZ123/bb6/actions/runs/42415186262), commit cbc22e8e9e2804b584b8707ac397eb872a53a695.

Axiom audit from that run:

| Declaration | Axioms |
|---|---|
| b0_even_prefix_to_b0_exact | propext, Classical.choice, Quot.sound |
| b0_odd_even_chain_to_b0_exact | propext, Classical.choice, Quot.sound |
| b0_even_prefix_to_b0_preserves_NoLeft4 | propext, Classical.choice, Quot.sound |
| b0_odd_even_chain_to_b0_preserves_NoLeft4 | propext, Classical.choice, Quot.sound |
| oddEvenShieldCounterexample_NoLeft4 | propext, Quot.sound |
| oddEvenShieldCounterexample_run_summary | none |
| oddEvenShieldCounterexample_run_not_NoLeft4 | propext, Quot.sound |

The workflow rejects sorryAx. The exact return theorems use the existing existential Reach-preserving return proofs, hence Classical.choice; the new tape and shield arguments introduce no additional nonstandard axiom.

The same run executes the 10,000,000-step raw-machine audit in test-root119-two-wave-census.cjs:

| Family | Shielded inputs | Shielded outputs | Boundary-safe inputs |
|---|---:|---:|---:|
| Even prefix | 21/21 | 21/21 | not required |
| Odd-even prefix | 22/22 | 22/22 | 22/22 |

These counts are finite observations along the blank-root orbit. They are not substitutes for the conditional Lean theorems or an all-time orbit proof.

The audit was extended to all reached B/0 states with left suffix 101. Among 7,367 such states, the left-six-bit distribution (from h-6 through h-1) was:

| Left six bits | Count |
|---|---:|
| 010101 | 7,279 |
| 000101 | 77 |
| 101101 | 8 |
| 100101 | 2 |
| 110101 | 1 |

The sole boundary-unsafe state is at raw time 3,193,243, head -689. Its right window h+1 through h+10 is 1111111111, and the prefix classifier labels it prefixUnmatched with m=401. The six bits beginning at h+m are 010101, so h+402=1 prevents the required odd-even terminal-zero corridor. It is not an odd-even prefix input. In contrast, the 22 odd-even inputs have left-six patterns 010101 (21 cases) and 000101 (one case); all satisfy the boundary condition. The 21 even-prefix inputs all have 010101.

This is a useful structural lead: the only observed reachable 110101 context is attached to a long unmatched right-one run, while every actual odd-even terminal-zero corridor is boundary-safe. It does not prove that Reach plus the odd-even corridor implies the guard. That implication remains the next formal target.

## Next mathematical question

Can the reachability hypothesis, together with the odd-even return's existing local tape assumptions and NoLeft4, prove the boundary condition

\[
\neg(t(h-6)=1\land t(h-5)=1\land t(h-4)=0)?
\]

The synthetic obstruction is not known to be reachable. A proof of this implication would remove the only extra shield hypothesis from the odd-even return on the authentic reachable orbit. A reachable counterexample would instead identify a genuine failure of this proposed shield. The 22 observed cases all satisfy the condition, but the universal implication remains open.

This work remains intermediate research in im-results/. It is not a complete B/0 classification, a blank-start halting decision, or a BB(6) upper bound.
