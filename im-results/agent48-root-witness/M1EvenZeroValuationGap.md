# M1 marker-1 valuation source: row 32 and the 24-cycle

**Status:** a complete source-level Lean composition has been written, including the q4 suffix and counted drain. It is **not yet compile-certified**. The exact local preflight and then targeted CI are pending. Do not treat this note as a certified theorem until the exported transitive axiom checks pass.

## Root location and exact row

The existing authentic root prefix in TM63RootMiddle26.lean ends at
\[
s1Config\ L\ (16R-11)\ 0\ A\ 0\ B\ H,
\qquad R=tm63RootResidueSixK,
\]
with \(R\) odd. The established rows 27–31 lead to marker 1 with
\[
n=16R-16,\qquad m=1.
\]
The required row-32 transition is
\[
\operatorname{run}\ tm2\
  (\operatorname{proposedIncrementCost}\ 1\ n\ a\ b)\
  (s1Config\ L\ n\ 1\ a\ 0\ b\ h)
=
\operatorname{some}
  (s1Config\ L\ (n-1)\ 0\ (a+b+2)\ 0\ (2^b-1)\ (h+5+3b)).
\]

The source theorem is now present as
**BB6Coverage.Agent48M1EvenValuationCountedSource.m1EvenValuation_counted_increment_source**
in [M1EvenValuationSource.lean](../agent48-counted-inc0/M1EvenValuationSource.lean). It is stated for **every positive** \(n<2^L\), not just one residue or valuation class. Its factorization wrapper uses
\[
n=(2q+1)2^v,\quad q<2^{L-v-1}.
\]
The theorem requires only \(a>0\); it does not require \(v>0\).

## Correct bridge placement and exact cost

The earlier proposed placement of \(4(v_2(n)-1)\) state-1 hole shifts immediately after a \(12a+6\)-step prefix is rejected. The finite audit found that its required consecutive-one premise fails for \(a=10\), and the claimed state-1 endpoint fails for \(a=20\). The three-step hole-shift itself is sound; the placement was wrong. See sections 1–2 of [M1EvenState1SweepAudit.md](../agent24-champion-time/M1EvenState1SweepAudit.md).

The corrected bridge is placed **after** the existing counted left sweep of length \(3a+1\), cost \(9a+3\). With \(v=v_2(n)\), the exact source phases are:

1. A fixed six-step prelude reaches state 1 at the new head with a blank under it. The S1 encoding supplies \(3v+4\) consecutive ones to the left.
2. **state1SweptLeft (3*(v+1))** consumes the corresponding block of \(3(v+1)\) ones in \(9(v+1)\) steps.
3. A fixed four-step exit reaches state 4.
4. A fixed three-step setup reaches state 5.
5. **state5SweptRight (v+1)** consumes the \(3(v+1)\)-cell block written by the left sweep in \(3(v+1)\) steps.
6. A fixed one-step exit and a final three-cell state-4 scan reach the q4 cut.

The bridge phases cost
\[
6+9(v+1)+4+3+3(v+1)+1+3=12v+29.
\]
Together with the initial \(9a+3\) sweep and final \(3a\) scan, the q4 prefix costs
\[
(9a+3)+(12v+29)+3a=12a+12v+32.
\]

The Lean source proves the exact q4 cut stream at the original head \(h\):
\[
[true]\mathbin{++}d1pow(a)\mathbin{++}markerWord(0)
 \mathbin{++}d0\mathbin{++}binDec(L,n-1)\mathbin{++}lh.
\]
It also proves the q4 right shape: five ones at \(h,\ldots,h+4\), blanks at \(h+5,h+6\), the \(3(b+1)\)-one right counter block, and the blank tail.

The existing q4 suffix has length \(39+3b\). Its first four moves are split off because the q4 prefix ends at state 4, head \(h+4\); the remaining suffix is \(35+3b\). The target-left identity is
\[
s1LeftFacing\ L\ (n-1)\ 0\ (a+b+2)\ (2^b-1)
=
d0pow(b)\mathbin{++}d1pow(2)\mathbin{++}Q.drop(1),
\]
where \(Q\) is the q4 cut left stream above. This matches the generic q4_suffix_run_to_s1Config interface.

Since \(v_2((2q+1)2^v)=v\),
\[
(12a+12v+32)+(35+3b)
=67+12a+12v+3b
=\texttt{resetPrefixCost 1 n a b}.
\]
The existing s1Config_reset_prefix_then_counted_drain then drains the intermediate counter \(2^b-1\), using the bound \(2^b-1<2^{a+b+2}\) supplied by \(a>0\). The result is exactly the proposed full counted increment cost and endpoint.

The reproducible JavaScript probe M1EvenValuationBridgeProbe.mjs also checks the phase endpoints and the full original-head q4 cut contract across 480 cases (exact valuations v=1..8, five odd quotients, six unary values including a=0, and two right-counter values). Every case reaches state 4 at h+4 after 12a+12v+32 steps. This is finite simulation evidence only; the Lean source theorem is the intended proof.

## Current Lean artifacts

- [M1EvenValuationBridge.lean](../agent48-counted-inc0/M1EvenValuationBridge.lean): state-1/state-5 bridge and tape updates.
- [M1EvenValuationSource.lean](../agent48-counted-inc0/M1EvenValuationSource.lean): authentic S1 prefix, q4 cut streams and right shape, q4 suffix, reset intermediate, counted drain, and the all-positive-bounded-n wrapper.
- [TM63RootMiddle34.lean](../agent44-tm63-middle/TM63RootMiddle34.lean): public tm63_middle32_source and an unconditional source composition through middle row 34. The old conditional theorem name remains only as a backwards-compatible wrapper.

The root row-32 bounds are derived from the existing \(R\ge61\) and tm63_index1_lt_pow_length1 lemmas: \(0<16R-16<2^L\). Its unary parameter \(a\) is positive because it is a sum plus 2.

## 24-cycle relevance

For the marker-1 rows
\[
n_j=16R-16-24j=8(2R-2-3j),
\]
the parity split gives \(v_2(n_j)=3\) for odd \(j\), and \(v_2(n_j)\ge4\) for even \(j\). The new all-positive-n theorem covers both classes, including the valuation-4 rows; no separate \(v=3\), \(v=4\), or \(v\ge5\) source theorem is needed if this composition compiles. The remaining cycle work is the formal row-schedule/induction and its connection to the authentic middle-26 endpoint. Agent 42 has been redirected to that complementary cycle integration rather than duplicating the q4 cut.

## Validation gate and next action

Agent 24 independently reviewed the full source composition and found no substantive mathematical or API mismatch. That review is not a Lean compile certificate. Agent 7 has been asked to refresh main and locally compile the exact dependency chain, including M1EvenState1Sweep, M1EvenState5Sweep, M1EvenValuationBridge, M1EvenValuationSource, and TM63RootMiddle34.

The updated manual workflow agent42-champion-terminal-source.yml stages and compiles these modules and checks the final #print axioms output for sorryAx and native_decide. It has not been dispatched before local preflight. The next action is to resolve actual Lean diagnostics, run that targeted workflow, and only then promote any result to results/.
