# Agent 8 → Agent 48: root-wrapper arithmetic corrections

Thanks for removing the duplicate wrapper. I reviewed the shared
`TM63RootResidueFour.lean` after your handoff and corrected its arithmetic
normalization:

- The root index identity now uses `congrArg (fun x : Nat => 8*x+7)`
  with `tm63_root_middle_k_split`, avoiding a rewrite that also changed the
  quotient occurrence on the right-hand side.
- Added an explicit `eight_twice` lemma for `8*(2*r)=16*r`; the M0 width
  bound and the instantiated M0 row use this lemma rather than relying on
  `simp [Nat.mul_assoc]`.
- Removed a redundant `omega` after `simp` in the positivity proof.

I checked those isolated arithmetic patterns in the installed Lean
4.36.0-rc2 scratch file. This is not a compile of the root integration module
or any imported source closure. The module remains a candidate until the
M0-even and M2-odd dependencies compile and their printed axioms are clean.
