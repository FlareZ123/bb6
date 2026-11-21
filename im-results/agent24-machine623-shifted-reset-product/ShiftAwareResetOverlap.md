# Shift-aware reset overlap for the #623 root

**Status:** intermediate finite diagnostic and proof-architecture improvement. This is not an all-time root invariant and does not prove nonhalting.

## Motivation

The S-indexed mass window for a source state is
\[
W_S(a,d)=((x_i,y_i): k_S+2\le i<j_S-2),
\]
where
\[
B_S=\max(34\ell_S+140,36\ell_S+88),\qquad
3^{k_S}>B_S,\qquad 3^{j_S}>B_S^3.
\]
For a successor, the known shift bounds are
\[
\delta=k_S'-k_S\in\{0,1\},\qquad
\eta=j_S'-j_S\in\{0,1,2,3\},
\]
with \(\delta=1\Rightarrow\eta\ge1\). The old output overlap \([k_S+3,j_S-2)\) is contained in the successor's required middle interval.

A reset word found at the left edge of \(W_S\) can lose its first output digit when \(\delta=1\). The previous full-word nonmonochromaticity check alone is therefore not enough.

## Shift-robust reset predicate

A minimal reset word \(w\) (length 3--6) is *one-symbol-overlap robust* for branch \(L\) or \(R\) when the following holds:

For every initial state in that branch's full carry rectangle, the emitted \(x\)-digit suffix after deleting the first output digit must contain both a digit different from 0 and a digit different from 2. The checker also appends each of the nine possible next input digit-pairs and verifies the property remains true. This appended-symbol check is equivalent: from every transducer state, varying the next input \(x\)-digit realizes all three possible next output digits, so a monochromatic suffix would fail for some appended symbol.

The checker in [shift_aware_reset_scan.js](shift_aware_reset_scan.js) builds the exact 225-state L and 270-state R carry transducers, enumerates the minimal reset language recognized by the 263-state DFA, and checks this predicate for every initial carry state and every possible appended symbol. It also checks that each reset word synchronizes the complete branch transducer.

Results:

| Quantity | L | R |
|---|---:|---:|
| Minimal reset words | 8,088 | 8,088 |
| One-symbol-overlap robust words | 7,542 | 7,560 |
| Non-robust words | 546 | 528 |

The minimal-word counts by length are 159, 1,626, 3,087, and 3,216 for lengths 3, 4, 5, and 6 respectively. The enumeration uses the accepted language and the proper-contiguous-subword minimality test; it does not rely on the stale 29,445 count in the DFA JSON's older construction metadata.

## Why this predicate handles the window shift

Set the affine source-carry boundary at
\[
K=3^{k_S+1},
\]
so its first emitted digit is exactly at position \(k_S+2\), the first position of \(W_S\). Since \(B_S<3^{k_S}<K\), the source-correction carry bounds apply at this boundary.

If a reset word starts at offset \(s\) in \(W_S\), one may recompute the source carry directly at \(K_s=3^sK\). The correction bound is unchanged and \(B_S<K_s\). Thus arbitrary prefix digits need not be transported through a separate carry induction merely to locate the reset: the same source-carry rectangle theorem applies at the reset's own scale.

For a reset at offset \(s\):

- If \(\delta=0\), all output digits of the reset word lie in the successor's middle interval.
- If \(\delta=1\) and \(s\ge1\), all output digits still lie in that interval.
- If \(\delta=1\) and \(s=0\), the first output digit is omitted. The reset word's output suffix after deleting that digit is already nonmonochromatic by the robustness check. This suffix lies inside the old output overlap \([k_S+3,j_S-2)\), hence inside the successor's required middle interval.

Consequently, a sufficient shift-aware witness is: any reset word if \(\delta=0\); if \(\delta=1\), either a reset word beginning at offset at least 1, or a one-symbol-overlap robust reset word beginning at offset 0.

This is a local implication, conditional on the source-carry bounds, sector/branch identification, and the affine-output/transducer digit correspondence. It avoids silently assuming that the full reset-word output survives a low-end truncation.

## Finite source-trace diagnostic

Using the conservative \(B_S\) above and the source-faithful highLevelNext recurrence mirror, the checker scans the 9,968 transitions
\[
D(33)\to D(34),\ldots,D(10000)\to D(10001).
\]
For each source state it scans the source S-window, computes the actual window-index shifts, and searches for a shift-aware witness using the branch associated with the source sector (LO/LE: L; RO/RE: R).

Observed results:

- 9,968/9,968 transitions have a shift-aware witness; zero failures.
- Window lengths range from 8 through 16.
- Shift pairs \((\delta,\eta)\): (0,0) 9,955; (0,1) 8; (1,1) 5.
- Source sectors select L on 4,096 transitions and R on 5,872.
- The first reset witness begins at offset 0 in 5,254 windows; in 4,714 it begins later. Among the left-edge first witnesses, 4,566 are robust for the selected branch and 688 are not. The non-robust left-edge cases do not cause a scan failure because the shift-aware search can use a later witness or the shift is zero.

This is computational evidence over a finite prefix only. The branch association is checked against the recurrence mirror on that prefix; its all-time use remains conditional on proving the cone/sector invariant.

## Remaining proof obligations

1. Prove that every future authentic S-window contains a shift-aware witness. The 9,968-state scan does not establish this induction.
2. Formalize the finite one-symbol-overlap robustness certificate in Lean, or provide a smaller verified certificate for the 8,088 reset words and both carry rectangles.
3. Extend the existing left_tail_step / right_tail_step affine quotient identities to an arbitrary reset word of length 3--6, so the transducer's emitted digits are rigorously identified with the actual successor-coordinate digits at the shifted boundary.
4. Prove the source-connected cone and sector/branch invariant, and the all-time S-window shift bounds.
5. Only after these close does reset acceptance yield the central-block nonmonochromaticity needed by the terminal-strip contradiction.

Relevant existing work: [RootPhaseInvariant](../agent32-623-phase-automaton/RootPhaseInvariant.md), [ResetPatternAudit](../agent49-parity623/ResetPatternAudit.md), [SourceCarryAffineBridge](../agent48-623-tight-window/SourceCarryAffineBridge.lean), and [SourceDerivedResetSourceBridge](SourceDerivedResetSourceBridge.lean).
