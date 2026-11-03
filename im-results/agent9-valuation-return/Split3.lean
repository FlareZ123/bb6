import ValuationReturn
namespace Agent9Val

def split3 (n : Nat) : Nat × Nat :=
  if h : n = 0 then (0, 0)
  else if n % 3 = 0 then
    let r := split3 (n/3)
    (r.1+1, r.2)
  else (0, n)
termination_by n

theorem split3_spec (n : Nat) (hn : 0 < n) :
    3^(split3 n).1 * (split3 n).2 = n ∧ (split3 n).2 % 3 ≠ 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hnot : n ≠ 0 := by omega
    have heq : split3 n = if n % 3 = 0 then
        let r := split3 (n/3)
        (r.1+1, r.2)
      else (0,n) := by
      rw [split3]
      simp [hnot]
    by_cases hmod : n % 3 = 0
    · have hsmaller : n/3 < n := by omega
      have hpositive : 0 < n/3 := by omega
      have ihh := ih (n/3) hsmaller hpositive
      simp only [heq, hmod, ite_true]
      constructor
      · calc
          3 ^ ((split3 (n/3)).1 + 1) * (split3 (n/3)).2 =
              3 * (3 ^ (split3 (n/3)).1 * (split3 (n/3)).2) := by
                simp [Nat.pow_succ]; ac_rfl
          _ = 3 * (n/3) := by rw [ihh.1]
          _ = n := by omega
      · exact ihh.2
    · simp [heq, hmod]

theorem nonzero_output_positive (q : Nat) (hq : 16 ≤ q) (_hnz : q%3 ≠ 0) :
    0 < onNZ q := by
  unfold onNZ
  by_cases h : q%3=1
  · simp only [ite_eq_left h]
    omega
  · simp only [ite_eq_right h]
    omega

theorem nonzero_core_exact (q c : Nat) (hq : 16 ≤ q)
    (hnz : q%3 ≠ 0) (h : (split3 (onNZ q)).1 ≤ c+incr q) :
    steps ((split3 (onNZ q)).1+1) (some (q,c)) =
      some (4^(split3 (onNZ q)).1*(split3 (onNZ q)).2,
            c+incr q-(split3 (onNZ q)).1) := by
  have hp := nonzero_output_positive q hq hnz
  have hh := (split3_spec (onNZ q) hp).1
  have heq : c+incr q = (c+incr q-(split3 (onNZ q)).1)+(split3 (onNZ q)).1 := by omega
  exact nonzero_core_burst q c _ _ _ hnz hh.symm heq

theorem nonzero_core_transfer_exact (q c : Nat) (hq : 16 ≤ q)
    (hnz : q%3≠0) (h : c+incr q < (split3 (onNZ q)).1) :
    steps (c+incr q+2) (some (q,c)) = none := by
  have hp := nonzero_output_positive q hq hnz
  have hh := (split3_spec (onNZ q) hp).1
  have hn : (split3 (onNZ q)).1 =
      c+incr q+1 + ((split3 (onNZ q)).1-(c+incr q+1)) := by omega
  have heq : onNZ q = 3^(c+incr q+1) *
      (3^((split3 (onNZ q)).1-(c+incr q+1)) * (split3 (onNZ q)).2) := by
    calc
      onNZ q = 3^(split3 (onNZ q)).1 * (split3 (onNZ q)).2 := hh.symm
      _ = 3^(c+incr q+1 + ((split3 (onNZ q)).1-(c+incr q+1))) *
          (split3 (onNZ q)).2 :=
            congrArg (fun e : Nat => 3^e * (split3 (onNZ q)).2) hn
      _ = 3^(c+incr q+1) *
          (3^((split3 (onNZ q)).1-(c+incr q+1)) * (split3 (onNZ q)).2) := by
            simp [Nat.pow_add, Nat.mul_assoc]
  exact nonzero_then_transfer q c _ hnz heq

#print axioms split3_spec
#print axioms nonzero_core_exact
#print axioms nonzero_core_transfer_exact

end Agent9Val
