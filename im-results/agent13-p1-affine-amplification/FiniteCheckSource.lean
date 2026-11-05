import AffineSourceList

namespace BB6.Agent13Affine

/-- Entirely computable original-shadow closure checker for a fixed finite graph. -/
def FiniteClosed (q side K : Nat) (nodes : List (Nat × Nat)) : Bool :=
  nodes.all (fun p =>
    (List.range K).all (fun t =>
      if h : p.2 % 2^t = 0 then
        let v := p.2 / 2^t
        let n := 16*q+side+p.1+t+v
        if hn : n % 2 = 1 then
          decide ((p.1+t+1, (n-1)/2) ∈ nodes)
        else true
      else true))

theorem all_mem {α : Type} (xs : List α) (f : α → Bool)
    (hall : xs.all f = true) (x : α) (hx : x ∈ xs) : f x = true := by
  induction xs with
  | nil => cases hx
  | cons a as ih =>
      have hc : f a && as.all f = true := by
        simpa [List.all] using hall
      obtain ⟨ha,ht⟩ := Bool.and_eq_true.mp hc
      rcases (List.mem_cons).mp hx with heq | htail
      · subst x
        exact ha
      · exact ih ht x htail

/-- Finite Boolean check entails complete closure under all exact source
    shadow transitions. No missing large inverse depths. -/
theorem finite_closed_sound
    (q side K : Nat) (nodes : List (Nat × Nat))
    (hbounded : nodes.all (fun p => decide (0 < p.2 ∧ p.2 < 2^K)) = true)
    (hclosed : FiniteClosed q side K nodes = true)
    (m z t v zp : Nat)
    (hmem : (m,z) ∈ nodes)
    (hdiv : z = 2^t*v)
    (hnext : 2*zp+1=16*q+side+m+t+v) :
    (m+t+1,zp) ∈ nodes := by
  have hz : 0<z ∧ z<2^K := of_decide_true
    (all_mem nodes (fun p => decide (0<p.2 ∧ p.2<2^K))
      hbounded (m,z) hmem)
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
  have hp := all_mem nodes
    (fun p => (List.range K).all (fun t =>
      if h : p.2 % 2^t = 0 then
        let v := p.2 / 2^t
        let n := 16*q+side+p.1+t+v
        if hn : n % 2 = 1 then
          decide ((p.1+t+1,(n-1)/2) ∈ nodes)
        else true
      else true))
    (by simpa only [FiniteClosed] using hclosed) (m,z) hmem
  have hp2 := all_mem (List.range K)
    (fun t =>
      if h : z % 2^t = 0 then
        let v := z / 2^t
        let n := 16*q+side+m+t+v
        if hn : n % 2 = 1 then
          decide ((m+t+1,(n-1)/2) ∈ nodes)
        else true
      else true)
    hp t hmemt
  have hd0 : z % 2^t = 0 := by rw [hdiv]; simp
  have hv : z/2^t=v := by
    rw [hdiv]
    exact Nat.mul_div_cancel_left v (2^t)
  have hn : (16*q+side+m+t+z/2^t) % 2 = 1 := by
    rw [hv]
    omega
  have hr : decide ((m+t+1,(16*q+side+m+t+z/2^t-1)/2)∈nodes) = true := by
    simpa only [hd0, hn, dite_true] using hp2
  have hzcalc : (16*q+side+m+t+z/2^t-1)/2=zp := by
    rw [hv]
    omega
  simpa only [hzcalc] using of_decide_true hr

#print axioms finite_closed_sound
end BB6.Agent13Affine
