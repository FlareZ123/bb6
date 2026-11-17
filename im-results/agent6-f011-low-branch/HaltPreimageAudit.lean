import Lean

/-!
Standalone audit of the exceptional p = false, r = 2, d = 3 branch for F011 (#464).

The function below is a literal transcription of upstream highLevelNext at
google-deepmind/cryptids commit
c86f15861709b76042998c5211c7b2f83991621b, file
BusyBeaver/BB6/M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD.lean, lines 1181-1221.

This file deliberately avoids the upstream dependency closure. It certifies the
branch calculation against this transcription; it is not an import-based
source-chain certificate for the upstream module.
-/

inductive AuditState where
  | S : Bool → Nat → Nat → AuditState
  deriving DecidableEq

def auditHighLevelNext : AuditState → Option AuditState
  | .S p k c =>
    let q := k / 3
    let r := k % 3
    if c < q then some (.S p (k - 3 * c - 2) (4 * c + 5))
    else
      let d := c - q
      if p then
        if r = 0 then
          if q = 0 then some (.S false 2 (c + 2))
          else if d = 0 then some (.S false 4 (4 * q + 5))
          else if d = 1 then some (.S false 1 (4 * q + 9))
          else if d = 2 then some (.S true (4 * q + 8) 1)
          else some (.S true (4 * q + 7) (d - 2))
        else if r = 1 then
          if d = 0 then some (.S false 8 (4 * q + 1))
          else if d = 1 then some (.S false (4 * q + 7) 1)
          else some (.S false (4 * q + 6) (d - 1))
        else
          if d = 0 then some (.S true 0 (4 * q + 5))
          else if d = 1 then some (.S false 0 (4 * q + 9))
          else if d = 2 then none
          else if d = 3 then some (.S false (4 * q + 10) 0)
          else if d = 4 then some (.S false (4 * q + 10) 3)
          else some (.S false (4 * q + 12) (d - 5))
      else
        if r = 0 then
          if q = 0 then
            if c = 0 then some (.S false 2 3) else some (.S false 4 (c - 1))
          else if d = 0 then some (.S true (4 * q) 1)
          else some (.S true (4 * q - 1) d)
        else if r = 1 then
          if d = 0 then some (.S false 0 (4 * q + 3))
          else if d = 1 then some (.S false (4 * q + 4) 1)
          else some (.S false (4 * q + 3) (d - 1))
        else
          if d = 0 then some (.S false 0 (4 * q + 5))
          else if d = 1 then none
          else if d = 2 then some (.S false (4 * q + 6) 0)
          else if d = 3 then some (.S false (4 * q + 6) 3)
          else some (.S false (4 * q + 8) (d - 4))

theorem p0_r2_d3_branch_exact (q : Nat) :
    auditHighLevelNext (.S false (3 * q + 2) (q + 3)) = some (.S false (4 * q + 6) 3) := by
  have hdiv : (3 * q + 2) / 3 = q := by
    apply Nat.div_eq_of_lt_le
    · simpa [Nat.mul_comm] using Nat.le_add_right (3 * q) 2
    · have hmul : (q + 1) * 3 = 3 * q + 3 := by
        simp [Nat.add_mul, Nat.mul_comm]
      rw [hmul]
      exact Nat.add_lt_add_left (Nat.lt_succ_self 2) (3 * q)
  have hmod : (3 * q + 2) % 3 = 2 := by
    have h := Nat.div_add_mod (3 * q + 2) 3
    rw [hdiv] at h
    exact Nat.add_left_cancel h
  simp [auditHighLevelNext, hdiv, hmod]

theorem p0_r2_d3_not_H0 (q Q : Nat) :
    auditHighLevelNext (.S false (3 * q + 2) (q + 3)) ≠
      some (.S false (3 * Q + 2) (Q + 1)) := by
  intro h
  have hbranch := p0_r2_d3_branch_exact q
  rw [hbranch] at h
  have hh : AuditState.S false (4 * q + 6) 3 = AuditState.S false (3 * Q + 2) (Q + 1) := by
    injection h
  injection hh with hp hk hc
  have hQ : Q = 2 := by
    have hc' : Q + 1 = 2 + 1 := by simpa using hc.symm
    exact Nat.add_right_cancel hc'
  subst Q
  have hnot : 4 * q + 6 ≠ 8 := by
    intro heq
    rcases Nat.eq_zero_or_pos q with hq0 | hqpos
    · subst q
      simp at heq
    · have hq1 : 1 ≤ q := Nat.succ_le_iff.mpr hqpos
      have h10 : 10 ≤ 4 * q + 6 := by
        calc
          10 = 4 * 1 + 6 := by decide
          _ ≤ 4 * q + 6 :=
            Nat.add_le_add_right (Nat.mul_le_mul_left 4 hq1) 6
      have hbad : ¬ 10 ≤ 8 := by decide
      apply hbad
      simpa [heq] using h10
  exact hnot (by simpa using hk)

theorem p0_r2_d3_not_H1 (q Q : Nat) :
    auditHighLevelNext (.S false (3 * q + 2) (q + 3)) ≠
      some (.S true (3 * Q + 2) (Q + 2)) := by
  intro h
  have hbranch := p0_r2_d3_branch_exact q
  rw [hbranch] at h
  have hh : AuditState.S false (4 * q + 6) 3 = AuditState.S true (3 * Q + 2) (Q + 2) := by
    injection h
  injection hh with hp
  cases hp

#print axioms p0_r2_d3_branch_exact
#print axioms p0_r2_d3_not_H0
#print axioms p0_r2_d3_not_H1
