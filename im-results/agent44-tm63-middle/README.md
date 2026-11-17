# TM63 marker-2 even (n=8q+6) source row

**Status:** source-level Lean draft; local preflight and manual CI acceptance have not yet completed. This is an intermediate component of the TM63 middle itinerary, not a BB(6) result.

## Generic mathematical statement

For (L,q,a,b\in\mathbb N), (h\in\mathbb Z), (3\le L), (8q+6<2^L), and (a>0), `M2EvenSixGenericSource.lean` states

\[
\begin{aligned}
&\operatorname{run}\ tm2\ (\operatorname{resetPrefixCost}\ 2\ (8q+6)\ a\ b)\\
&\qquad(s1Config\ L\ (8q+6)\ 2\ a\ 0\ b\ h)\\
&=\operatorname{some}\bigl(s1Config\ L\ (8q+5)\ 1\ (a+b+2)\ (2^b-1)\ 0\ (h+5+3b)\bigr).
\end{aligned}
\]

The main theorem is `m2EvenSix_generic_q4_reset_prefix_source`. It lifts the fixed (L=3,n=6) q4 prefix in `M2EvenSixQ4Prefix.lean) to arbitrary (q) by a finite-window frame. The input and target binary encodings share a common tail after the three low bits; the proof isolates the region visited by the (44+12a)-step prefix, proves a uniform head lower bound, and preserves the q4 right guard and far-right blank tail before composing the existing q4 suffix.

`M2EvenSixGenericCounted.lean` composes this reset-prefix theorem with the existing S1 counted drain. Its theorem `m2EvenSix_generic_counted_increment_source` gives the full proposed increment:

\[
\operatorname{run}\ tm2\ (\operatorname{proposedIncrementCost}\ 2\ (8q+6)\ a\ b)
(s1Config\ L\ (8q+6)\ 2\ a\ 0\ b\ h)
=
\operatorname{some}\bigl(s1Config\ L\ (8q+5)\ 1\ (a+b+2)\ 0\ (2^b-1)\ (h+5+3b)\bigr).
\]

The first theorem ends with the all-ones left counter ((2^b-1)) and zero right counter; the counted adapter drains that counter and swaps the final two counter arguments. This is an original-`tm2` source statement, not a copied transition system.

## Root specialization and dependency

Let (R=tm63RootResidueSixK), which the root arithmetic proves odd. The root's marker-2 row 34 has

\[
n=16R-18=8(2R-3)+6,
\]

so the generic quotient is (q=2R-3), also odd. This row is downstream of two earlier rows:

| Row | Input marker | Input index | Status |
|---:|---:|---:|---|
| 32 | 1 | (16R-16=32((R-1)/2)) | First missing source transition: the M1-even arbitrary-valuation bridge |
| 33 | 0 | (16R-17) | Existing all-odd M0 source increment |
| 34 | 2 | (16R-18=8(2R-3)+6) | This generic M2-even-six source theorem |

`TM63RootMiddle34.lean` composes the existing rows 27–31, exposes the exact row-32 M1-even run as its **single explicit hypothesis**, and then composes rows 33–34. Under that hypothesis it reaches the authentic blank-root configuration at marker 1 and index (16R-19). The conditional theorem is `tm63_blank_reaches_after_middle34_of_m1even32`.

This is a useful root integration boundary, not an unconditional root extension. It does not bypass row 32, establish the full 24-cycle induction, prove the later itinerary or halt, or determine BB(6).


## Whole-section original-run composition

`SectionResultRunSource.lean` adds a reusable conditional theorem: if a single original-`tm2` counted-increment source theorem is available for every (0<k<2^L), then the complete primitive-recursive `sectionResult` stage is itself an original-`tm2` run. The proof is induction on the stage length, composing each increment with `run_add`; it carries the moving head through `sectionHeadAfter`, with the closed form
[
  H(n,b)=5n+3\,sumRight(n,b).
]
The recurrence (H(n+1,b)=5+3b+H(n,nextRight(b))) matches the per-increment head shift exactly.

This is a composition theorem, not a proof of the universal macro premise. The remaining work is to assemble a total one-step dispatcher over the reachable ((m\bmod3,n\bmod8)) classes. The M1-even full counted theorem and M2-even-six generic theorem are critical cases. Once the dispatcher is source-proved, this lemma offers a direct route through the entire middle `sectionResult` without manually enumerating every 24-periodic row.

## Verification and next work

- The generic prefix source and its three `#print axioms` declarations are in `M2EvenSixGenericSource.lean`.
- The counted adapter is in `M2EvenSixGenericCounted.lean`.
- The conditional root composition is in `TM63RootMiddle34.lean`.
- A targeted local preflight has been requested from Agent 4. No successful compile/axiom audit for these new modules is claimed yet.
- The existing manual `.github/workflows/agent42-champion-terminal-source.yml` now stages and compiles the generic source, counted adapter, and conditional root theorem in the same source closure as the existing middle rows. It has not yet been dispatched. No per-commit workflow was added.

Next useful work is to resolve the first concrete local compiler error, then perform one manual source-closure CI acceptance run and inspect the final axiom output. Once the independent M1-even row-32 theorem is source-checked, instantiate the hypothesis in `TM63RootMiddle34.lean` and continue the 24-cycle root induction. Keep this dossier in `im-results/`; nothing here is ready for `results/`.
