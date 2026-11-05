import AffineSourceList

namespace BB6.Agent13Affine

/-- A finite list's exact integer transition-closure test, checked entirely
    by Lean kernel reduction.  The only t values considered are 0,...,K-1. -/
def FiniteClosed (q side K : Nat) (nodes : List (Nat × Nat)) : Prop :=
  nodes.Forall (fun p =>
    (List.range K).Forall (fun t =>
      p.2 % 2^t = 0 →
      let v := p.2 / 2^t
      let n := 16*q+side+p.1+t+v
      n % 2 = 1 →
      (p.1+t+1, (n-1)/2) ∈ nodes))

theorem all_mem {α : Type} {P : α → Prop} (xs : List α)
    (hall : xs.Forall P) (x : α) (hx : x ∈ xs) : P x := by
  induction hall with
  | nil => cases hx
  | @cons a as ha hs ih =>
      simp only [List.mem_cons] at hx
      rcases hx with heq | htail
      · subst x
        exact ha
      · exact ih htail

/-- Soundness of the automatically decidable finite-graph closure test.
    No unbounded enumeration, assumed dynamics, or native reduction. -/
theorem finite_closed_sound
    (q side K : Nat) (nodes : List (Nat × Nat))
    (hbounded : nodes.Forall (fun p => 0 < p.2 ∧ p.2 < 2^K))
    (hclosed : FiniteClosed q side K nodes)
    (m z t v zp : Nat)
    (hmem : (m,z) ∈ nodes)
    (hdiv : z = 2^t*v)
    (hnext : 2*zp+1=16*q+side+m+t+v) :
    (m+t+1,zp) ∈ nodes := by
  have hz := all_mem nodes hbounded (m,z) hmem
  have ht : t<K := by
    by_contra hn
    have hge : K≤t := by omega
    have hd : 2^K ∣ 2^t := Nat.pow_dvd_pow 2 hge
    have hd2 : 2^K ∣ z := by
      rw [hdiv]
      exact dvd_mul_of_dvd_left hd v
    have hmin : 2^K ≤ z := Nat.le_of_dvd hz.1 hd2
    omega
  have hmemt : t ∈ List.range K := by simpa using ht
  have hp := all_mem nodes hclosed (m,z) hmem
  have hp2 := all_mem (List.range K) hp t hmemt
  have hd0 : z % 2^t = 0 := by
    rw [hdiv]
    simp
  have hv : z/2^t=v := by
    rw [hdiv]
    exact Nat.mul_div_cancel_left v (2^t)
  have hn : (16*q+side+m+t+z/2^t) % 2 = 1 := by
    rw [hv]
    omega
  have hr := hp2 hd0 hn
  have hzz : (16*q+side+m+t+z/2^t-1)/2=zp := by
    rw [hv]
    omega
  simpa only [hzz] using hr

#print axioms finite_closed_sound
end BB6.Agent13Affine
