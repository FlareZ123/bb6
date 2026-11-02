import Lean.Elab.Tactic.Omega

namespace BB6.Agent24.Coding

/-- The shift-conjugate of Machine B's scalar map. -/
def T (v : Nat) : Nat := (3*v + 7*(v%2))/2

def path (v : Nat) : Nat → Nat
  | 0 => v
  | i+1 => T (path v i)

theorem path_step (v i : Nat) :
    2*path v (i+1) = 3*path v i + 7*(path v i%2) := by
  dsimp [path,T]
  omega

/-- Matching length-n parity prefixes force initial values to coincide modulo 2^n. -/
theorem prefix_forces_divisor (a b n : Nat)
    (hab : a ≤ b)
    (hp : ∀ i : Nat, i < n → (path a i)%2 = (path b i)%2) :
    2^n ∣ b-a := by
  have ho : ∀ i : Nat, i ≤ n → path a i ≤ path b i := by
    intro i
    induction i with
    | zero =>
        intro _
        simpa [path] using hab
    | succ i ih =>
        intro hi
        have hi' : i < n := by omega
        have hprev := ih (by omega)
        have h1 := path_step a i
        have h2 := path_step b i
        have he := hp i hi'
        omega
  let d (i : Nat) : Nat := path b i - path a i
  have hd (i : Nat) (hi : i < n) : 2*d (i+1) = 3*d i := by
    have hprev := ho i (by omega)
    have hnext := ho (i+1) (by omega)
    have h1 := path_step a i
    have h2 := path_step b i
    have he := hp i hi
    dsimp [d]
    omega
  have hmul : ∀ i : Nat, i ≤ n → 2^i*d i = 3^i*d 0 := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
        intro hi
        have hi' : i < n := by omega
        have hp' := ih (by omega)
        calc
          2^(i+1)*d (i+1) = 2^i*(2*d (i+1)) := by rw [Nat.pow_succ]; ac_rfl
          _ = 2^i*(3*d i) := by rw [hd i hi']
          _ = 3*(2^i*d i) := by ac_rfl
          _ = 3*(3^i*d 0) := by rw [hp']
          _ = 3^(i+1)*d 0 := by rw [Nat.pow_succ]; ac_rfl
  have hdiv : 2^n ∣ d 0 := by
    apply (Nat.Coprime.pow n n (by decide : Nat.Coprime 2 3)).dvd_of_dvd_mul_left
    exact ⟨d n, (hmul n (by omega)).symm⟩
  exact hdiv

/-- Two distinct inputs with gap less than 2^n have distinct length-n parity prefixes. -/
theorem finite_prefix_separates (a b n : Nat)
    (hab : a < b) (hgap : b-a < 2^n) :
    ∃ i : Nat, i < n ∧ (path a i)%2 ≠ (path b i)%2 := by
  classical
  by_cases hex : ∃ i : Nat, i < n ∧ (path a i)%2 ≠ (path b i)%2
  · exact hex
  · have hp (i : Nat) (hi : i < n) : path a i%2 = path b i%2 := by
      by_cases h : path a i%2 = path b i%2
      · exact h
      · exact False.elim (hex ⟨i,hi,h⟩)
    have hd := prefix_forces_divisor a b n (by omega) hp
    have hpos : 0 < b-a := by omega
    have hle := Nat.le_of_dvd hpos hd
    omega

#print axioms prefix_forces_divisor
#print axioms finite_prefix_separates
end BB6.Agent24.Coding
