import PeriodicGridPacking

namespace ValuationPacking

def Witness (K : Nat) (v k z : Nat) : Prop :=
  0 < v ∧ 3*v < K ∧ 0 < k ∧ 4^k*z = v+K

theorem quotient_injective (K v w k l z : Nat)
    (hv : Witness K v k z) (hw : Witness K w l z) :
    v = w ∧ k = l := by
  rcases hv with ⟨hvpos,hvupper,hkpos,hvscale⟩
  rcases hw with ⟨hwpos,hwupper,hlpos,hwscale⟩
  have hkl : k = l := by
    by_cases hlt : k < l
    · have hpow : 4^(k+1) ≤ 4^l :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hprod := Nat.mul_le_mul_right z hpow
      have hfour : 4^(k+1)*z = 4*(4^k*z) := by
        rw [Nat.pow_succ]
        grind
      rw [hfour,hvscale,hwscale] at hprod
      omega
    · by_cases hlt2 : l < k
      · have hpow : 4^(l+1) ≤ 4^k :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hprod := Nat.mul_le_mul_right z hpow
        have hfour : 4^(l+1)*z = 4*(4^l*z) := by
          rw [Nat.pow_succ]
          grind
        rw [hfour,hwscale,hvscale] at hprod
        omega
      · omega
  constructor
  · rw [hkl] at hvscale
    omega
  · exact hkl

theorem quotient_good (K v k z : Nat) (h : Witness K v k z) :
    0 < z ∧ z < K ∧ (12*z < K ∨ (K < 4*z ∧ 3*z < K)) := by
  rcases h with ⟨hvpos,hvupper,hkpos,hscale⟩
  have hzp : 0 < z := by
    by_cases hz : z = 0
    · simp [hz] at hscale
      omega
    · omega
  constructor
  · exact hzp
  constructor
  · by_cases hk : k = 1
    · rw [hk] at hscale
      change 4*z = v+K at hscale
      omega
    · have hk2 : 2 ≤ k := by omega
      have hpow : 4^2 ≤ 4^k := Nat.pow_le_pow_right (by omega) hk2
      have hprod := Nat.mul_le_mul_right z hpow
      simp only [show (4:Nat)^2 = 16 by decide] at hprod
      rw [hscale] at hprod
      omega
  · by_cases hk : k = 1
    · right
      rw [hk] at hscale
      change 4*z = v+K at hscale
      omega
    · left
      have hk2 : 2 ≤ k := by omega
      have hpow : 4^2 ≤ 4^k := Nat.pow_le_pow_right (by omega) hk2
      have hprod := Nat.mul_le_mul_right z hpow
      simp only [show (4:Nat)^2 = 16 by decide] at hprod
      rw [hscale] at hprod
      omega

structure Point (K : Nat) where
  v : Nat
  k : Nat
  z : Nat
  witness : Witness K v k z

private theorem quotient_nodup (K : Nat) (l : List (Point K))
    (h : (l.map (fun p => (p.v,p.k))).Nodup) :
    (l.map (fun p => p.z)).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons] at h ⊢
    obtain ⟨hnot, hxs⟩ := List.nodup_cons.mp h
    apply List.nodup_cons.mpr
    constructor
    · intro hz
      obtain ⟨y, hy, he⟩ := List.mem_map.mp hz
      have heq := quotient_injective K x.v y.v x.k y.k x.z
        x.witness (by simpa [he] using y.witness)
      apply hnot
      exact List.mem_map.mpr ⟨y, hy, by exact Prod.ext heq.1.symm heq.2.symm⟩
    · exact ih hxs

theorem finite_valuation_packing_pairs (K : Nat) (l : List (Point K))
    (h : (l.map (fun p => (p.v,p.k))).Nodup) :
    l.length ≤ (K-1)/6 := by
  have hn := quotient_nodup K l h
  have hg : ∀ z, z ∈ l.map (fun p => p.z) → PeriodicGrid.Good K z := by
    intro z hz
    obtain ⟨p, hp, he⟩ := List.mem_map.mp hz
    have q := quotient_good K p.v p.k p.z p.witness
    simpa only [PeriodicGrid.Good, ← he] using q
  have pack := PeriodicGrid.grid_packing_all K (l.map (fun p => p.z)) hn hg
  simpa only [List.length_map] using pack

theorem finite_valuation_packing (K : Nat) (l : List (Point K))
    (h : (l.map (fun p => p.v)).Nodup) :
    l.length ≤ (K-1)/6 := by
  have hpairs : (l.map (fun p => (p.v,p.k))).Nodup := by
    induction l with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons] at h ⊢
      obtain ⟨hnot,hxs⟩ := List.nodup_cons.mp h
      apply List.nodup_cons.mpr
      constructor
      · intro hm
        obtain ⟨y,hy,he⟩ := List.mem_map.mp hm
        apply hnot
        exact List.mem_map.mpr ⟨y,hy, congrArg Prod.fst he⟩
      · exact ih hxs
  exact finite_valuation_packing_pairs K l hpairs

#print axioms quotient_injective
#print axioms quotient_good
#print axioms finite_valuation_packing_pairs
#print axioms finite_valuation_packing
end ValuationPacking
