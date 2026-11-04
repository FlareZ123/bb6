import Lean.Elab.Tactic.Omega

namespace NeedleGap

private theorem linear_bound (v : Nat) (hv : 5 ≤ v) :
    v + 3 ≤ 2^(v-2) := by
  obtain ⟨w,hw⟩ : ∃ w, v = 5+w := ⟨v-5, by omega⟩
  subst v
  induction w with
  | zero => decide
  | succ w ih =>
    have he : 5+(w+1)-2 = (5+w-2)+1 := by omega
    rw [he, Nat.pow_succ]
    have hp : 0 < (2:Nat)^(5+w-2) := Nat.pow_pos (by decide)
    have ih2 := ih (by omega : 5 ≤ 5+w)
    omega

private theorem gap_large (q v K : Nat) (hv : 5 ≤ v)
    (h : 2^v * (2*q+3) + v + 3*(q+1) = 2^K) :
    2*v+1 ≤ K := by
  have not_le : ¬ K ≤ 2*v := by
    intro hk
    have hp : 0 < (2:Nat)^v := Nat.pow_pos (by decide)
    have hqexp : 2^(v+1) * 2^(v-1) = (2:Nat)^(2*v) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hpow : (2:Nat)^K ≤ 2^(2*v) := Nat.pow_le_pow_right (by decide) hk
    have hq : q < 2^(v-1) := by
      apply Classical.byContradiction
      intro hnot
      have hle : 2^(v-1) ≤ q := by omega
      have hm := Nat.mul_le_mul_left (2^(v+1)) hle
      have hbigger : 2^(v+1)*q < 2^K := by
        have he : 2^(v+1)*q + 3*2^v + v+3*(q+1) =
          2^v*(2*q+3)+v+3*(q+1) := by
          rw [Nat.pow_succ]
          simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm]
        calc
          2^(v+1)*q < 2^(v+1)*q + 3*2^v + v+3*(q+1) := by omega
          _ = 2^K := by rw [he,h]
      omega
    have hlin := linear_bound v hv
    let t := (2:Nat)^(v-2)
    have ht : 0<t := Nat.pow_pos (by decide)
    have hp4 : (2:Nat)^v = 4*t := by
      calc
        (2:Nat)^v = 2^((v-2)+2) := by congr 1; omega
        _ = 4*t := by simp [t, Nat.pow_add, Nat.mul_comm]
    have hp2 : (2:Nat)^(v-1) = 2*t := by
      dsimp [t]
      have he : v-1 = (v-2)+1 := by omega
      rw [he, Nat.pow_succ]
      omega
    have h8 : (2:Nat)^(v+1) = 8*t := by
      rw [Nat.pow_succ, hp4]
      omega
    have hsbound : 0< 3*q+v+3 ∧ 3*q+v+3 < 2*2^v := by
      constructor
      · omega
      · rw [hp2] at hq
        rw [hp4]
        change v+3 ≤ t at hlin
        omega
    have hklo : v ≤ K := by
      apply Classical.byContradiction
      intro hh
      have hlow := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (by omega : K ≤ v)
      rw [←h] at hlow
      have h3 : 3*2^v ≤ 2^v*(2*q+3) := by
        have he : 3 ≤ 2*q+3 := by omega
        have hm := Nat.mul_le_mul_left (2^v) he
        omega
      omega
    let r := K-v
    have hkr : K=v+r := by dsimp [r]; omega
    have hmain : 2^v * 2^r = 2^v*(2*q+3)+(3*q+v+3) := by
      rw [←Nat.pow_add, ←hkr]
      omega
    have hrmin : 2*q+3 < 2^r := by
      apply Classical.byContradiction
      intro hnot
      have hle : 2^r ≤ 2*q+3 := by omega
      have hm := Nat.mul_le_mul_left (2^v) hle
      omega
    have hrmax : 2^r < 2*q+5 := by
      apply Classical.byContradiction
      intro hnot
      have hle : 2*q+5 ≤ 2^r := by omega
      have hm := Nat.mul_le_mul_left (2^v) hle
      have hprod : 2^v*(2*q+5) = 2^v*(2*q+3)+2*2^v := by
        calc
          2^v*(2*q+5) = 2^v*((2*q+3)+2) := by congr 1
          _ = 2^v*(2*q+3)+2*2^v := by rw [Nat.mul_add]; omega
      omega
    have hr : 2^r = 2*q+4 := by omega
    have hs : 3*q+v+3 = 2^v := by
      rw [hr] at hmain
      have he : 2^v*(2*q+4) = 2^v*(2*q+3)+2^v := by
        calc
          2^v*(2*q+4) = 2^v*((2*q+3)+1) := by congr 1
          _ = 2^v*(2*q+3)+2^v := by rw [Nat.mul_add]; omega
      omega
    have hid : 3*2^r+2*v = 2^(v+1)+6 := by
      rw [hr, Nat.pow_succ]
      omega
    have hrle : r ≤ v := by dsimp [r]; omega
    rcases Nat.lt_or_eq_of_le hrle with hlt | heq
    · have hpowr : (2:Nat)^r ≤ 2^(v-1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      rw [hp2] at hpowr
      rw [h8] at hid
      change v+3 ≤ t at hlin
      omega
    · rw [heq, hp4, h8] at hid
      omega
  omega

theorem gap_all (q v K : Nat)
    (h : 2^v * (2*q+3) + v + 3*(q+1) = 2^K) :
    2*v+1 ≤ K := by
  by_cases hv : 5 ≤ v
  · exact gap_large q v K hv h
  · by_cases hk : 2*v+1 ≤ K
    · exact hk
    · have hsmall : v ≤ 4 := by omega
      have hklo : K ≤ 8 := by omega
      have hvcases : v=0 ∨ v=1 ∨ v=2 ∨ v=3 ∨ v=4 := by omega
      have hkcases : K=0 ∨ K=1 ∨ K=2 ∨ K=3 ∨ K=4 ∨ K=5 ∨ K=6 ∨ K=7 ∨ K=8 := by omega
      rcases hvcases with hv0|hv1|hv2|hv3|hv4 <;>
        rcases hkcases with hk0|hk1|hk2|hk3|hk4|hk5|hk6|hk7|hk8 <;>
        subst v <;> subst K <;>
        simp at h <;> omega

end NeedleGap
#print axioms NeedleGap.gap_large
#print axioms NeedleGap.gap_all
