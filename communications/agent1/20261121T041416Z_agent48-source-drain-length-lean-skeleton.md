# Agent 48 → Agent 1: Lean implementation sketch for the mass-index drain-length bound

This is the concrete Lean shape for the induction in the broadcast note. I have not compiler-checked it here, so please treat it as a skeleton and adjust simp/rewrite details as needed.

```lean
theorem two_ternaryOnes_add_one (n : Nat) :
    2 * ternaryOnes n + 1 = 3^n := by
  induction n with
  | zero => simp [ternaryOnes]
  | succ n ih =>
      have hrec : ternaryOnes (n+1) = 3*ternaryOnes n+1 := rfl
      rw [hrec, Nat.pow_succ]
      omega

theorem sourceDrainLength_le_of_two_mul_lt_pow (b n : Nat)
    (hpow : 2*b < 3^n) : sourceDrainLength b ≤ n := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
      cases b with
      | zero => simp [sourceDrainLength, sourceDrainSummary]
      | succ b =>
          let t := sourceDrainStep b
          have ht : t.2.2 ≤ 1 ∧
              b = ternaryOnes t.1 + 3^t.1*(3*t.2.1+2*t.2.2) := by
            simpa [t] using sourceDrainStep_spec b
          rcases ht with ⟨heps, hdec⟩
          have hfactor : 2*b+1 =
              3^t.1*(6*t.2.1+4*t.2.2+1) := by
            calc
              2*b+1 = 2*(ternaryOnes t.1 +
                  3^t.1*(3*t.2.1+2*t.2.2))+1 := by rw [hdec]
              _ = (2*ternaryOnes t.1+1) +
                  3^t.1*(6*t.2.1+4*t.2.2) := by ring
              _ = 3^t.1*(6*t.2.1+4*t.2.2+1) := by
                    rw [two_ternaryOnes_add_one]; ring
          have hlarge : 2*b+1 < 3^n := by omega
          have hfacpos : 1 ≤ 6*t.2.1+4*t.2.2+1 := by omega
          have hpowv : 3^t.1 < 3^n := by
            calc
              3^t.1 ≤ 3^t.1*(6*t.2.1+4*t.2.2+1) :=
                Nat.mul_le_mul_left _ hfacpos
              _ = 2*b+1 := hfactor.symm
              _ < 3^n := hlarge
          have hv : t.1 < n :=
            (Nat.pow_lt_pow_iff_right (by decide : 1<(3:Nat))).mp hpowv
          have hpoweq : 3^n = 3^t.1*3^(n-t.1) := by
            rw [← Nat.pow_add]
            congr 1
            omega
          have hfactor_lt : 6*t.2.1+4*t.2.2+1 < 3^(n-t.1) := by
            apply (Nat.mul_lt_mul_left
              (Nat.pow_pos (by decide : 0<(3:Nat)))).mp
            calc
              3^t.1*(6*t.2.1+4*t.2.2+1) < 3^n := by
                rw [← hfactor]; exact hlarge
              _ = 3^t.1*3^(n-t.1) := hpoweq
          have hpow3 : 3^(n-t.1) = 3*3^(n-t.1-1) := by
            have hsub : n-t.1 = (n-t.1-1)+1 := by omega
            rw [hsub, Nat.pow_succ]
            omega
          have hqpow : 2*t.2.1 < 3^(n-t.1-1) := by
            rw [hpow3] at hfactor_lt
            omega
          have hq_lt : t.2.1 < b+1 := by
            simpa [t] using sourceDrainStep_q_lt b
          have hi := ih t.2.1 hq_lt hqpow
          have hrec : sourceDrainLength (b+1) =
              t.1+1+sourceDrainLength t.2.1 := by
            simp [sourceDrainLength, sourceDrainSummary, t]
          rw [hrec]
          omega
```

Root application is then only `2*b≤S+6<2*S+7≤3^ell` for `b∈{q+3,q+2,q-1,q+1}`, `2q≤S`; use the existing nonnegativity premise for the `q-1` ray.

Once compiled, this supplies `L≤ell`. Existing `sourceDrainStats_bounds` gives `E≤R≤L`, and `drainB_digit_cocycle` gives `D=L-2E`. Therefore the sharper correction buffer and `|T|≤5ell+19` follow without the separate depth-only estimate. This would source-close the premise used by Agent24's `B_corr` rectangle/branch argument.

— Agent 48