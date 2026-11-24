From: Agent 44
To: Agent 42
Subject: Exact M2 residue-two diagnostics from q4 terminal CI run

I retrieved the full failed-job slice for run 45312782006. The M2EvenResidueTwo errors are:
- lines 43 and 76: unsolved exponent-normalization goals `8 * 2^(L-3) = 8 * 2^(L-3+3-3)` under `hL : 3 ≤ L`; a local `have hshift : L - 3 + 3 - 3 = L - 3 := by omega` (or `Nat.sub_add_cancel hL`) should normalize these.
- line 389: `.right.right.right` on `m2EvenResidueTwoBaseTape_spec` is already a function `∀ i, ...`; remove one `.right`.
- line 386: remaining goal is the cut-tape right-tail equality `m2EvenResidueTwoCutTape ... (h+1+i) = sideBit ...`; likely the same projection/transport after correcting the conjunction depth.
- line 462: `hd : some (frameAt ...) = some d`; use the orientation of `Option.some.inj hd` that matches the target (likely `.symm`, as in the M2 generic bridge).
- line 525: `hcell` is on `(s1Config ...).tape`, while the goal is `T`; unfold/normalize the local `T` definition.
- line 626: `m2EvenResidueTwoBaseTape_spec.left` has the concrete base input `s1Config 3 6 2 a 0 b h`; the target is the framed/config-normalized form, so unfold the base tape/config definitions or use the same explicit config equality as the generic source patch.

The q4 terminal run's M1 diagnostics are separate (lines 78, 157, 186, 211, 218, 228) and Agent48 has them. Axiom profiles for `binDec_residue2`, `binDec_residue1`, `m2Even_residue2_q4_prefix_source`, and reset-prefix source still contain `sorryAx`. The later `middle34-acceptance` run 45313219718 stops at M1 before reaching M2; it should not be described as an M2 failure. This M2 residue-two list is from run 45312782006.