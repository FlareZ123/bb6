import EvenSector

namespace BB6.HaltingFunnel

/-- All outputs of the recursively accelerated drain have even left counter. -/
theorem G_left_even (k c : Nat) : (G k c).1 % 2 = 0 := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases h1 : c < 2*k
    · rw [G]
      simp only [h1, dite_true]
      exact ih _ (by omega) _
    · by_cases h2 : c ≤ 2*k+1
      · rw [G]
        simp only [h1, dite_false, h2, ite_eq_left]
      · rw [G]
        simp [h1,h2]
        omega

/-- At odd counter c with even left counter, the second or third step
    returns to an even-left-counter hub. The c=3 branch enters even c. -/
def U (a c : Nat) : Nat × Nat :=
  if c = 1 then (2, a+3)
  else if c = 3 then (2, a+6)
  else if c = 5 then G (a/2+1) 1
  else G (a/2+2) (c-4)

/-- At odd c=1, exactly two T evaluations make one return of U. -/
theorem U_one (a : Nat) :
    T a 1 = some (a+2,0) ∧ T (a+2) 0 = some (U a 1) := by
  constructor
  · simp [T]
  · simp [T,U]

/-- At odd c=3, exactly three T evaluations enter the even sector. -/
theorem U_three (a : Nat) (ha : a%2=0) :
    T a 3 = some (a+3,1) ∧
    T (a+3) 1 = some (a+5,0) ∧
    T (a+5) 0 = some (U a 3) := by
  have ht := T_even a 3 ha (by omega)
  constructor
  · simpa using ht
  constructor
  · simp [T]
  · simp [T,U]

/-- For odd c>=5, exactly two T evaluations collapse to U. -/
theorem U_large (a c : Nat) (ha : a%2=0) (hc : c%2=1) (h5 : 5≤c) :
    T a c = some (a+3,c-2) ∧
    T (a+3) (c-2) = some (U a c) := by
  have ht := T_even a c ha (by omega)
  constructor
  · exact ht
  · have hodd : (a+3)%2≠0 := by omega
    have hzero : c-2≠0 := by omega
    have hone : c-2≠1 := by omega
    have htwo : c-2≠2 := by omega
    have hquot : (a+3)/2 = a/2+1 := by omega
    by_cases h5eq : c=5
    · subst c
      simp [T,U,hodd, hquot]
    · have hne : c-2≠3 := by omega
      have hsub : c-2-2 = c-4 := by omega
      simp only [T, if_neg hzero, if_neg hone, if_neg hodd,
        if_neg htwo, if_neg hne]
      rw [hsub,hquot]
      have heu : U a c = G (a/2+2) (c-4) := by
        simp [U, show c≠1 by omega, show c≠3 by omega,
          show c≠5 by omega]
      rw [heu]

/-- The U-return always has even left counter. -/
theorem U_left_even (a c : Nat) (ha : a%2=0)
    (hc : c%2=1) : (U a c).1%2=0 := by
  by_cases h1 : c=1
  · simp [U,h1]
  · by_cases h3 : c=3
    · simp [U,h1,h3]
    · by_cases h5 : c=5
      · simp [U,h1,h3,h5,G_left_even]
      · simp only [U,if_neg h1,if_neg h3,if_neg h5]
        exact G_left_even _ _

/-- The only odd-sector hub that enters the even-counter sector on U is c=3. -/
theorem U_even_counter_iff_three (a c : Nat) (ha : a%2=0)
    (hc : c%2=1) : ((U a c).2%2=0 ↔ c=3) := by
  by_cases h1 : c=1
  · simp [U,h1]
    omega
  · by_cases h3 : c=3
    · simp [U,h1,h3]
      omega
    · by_cases h5 : c=5
      · subst c
        have hh := G_odd (a/2+1) 1 (by decide)
        have hne : (G (a/2+1) 1).2 % 2 ≠ 0 := by omega
        simp [U, hne]
      · have h4 : (c-4)%2=1 := by omega
        have hh := G_odd (a/2+2) (c-4) h4
        simp only [U,if_neg h1,if_neg h3,if_neg h5]
        omega

/-- At the unique odd-to-even return gateway (a,3), exact classification of
    subsequent halting without visiting another odd-c hub. -/
theorem U_three_clean_halt_iff (a : Nat) :
    (∃ steps, EvenHIn steps (U a 3).1 (U a 3).2) ↔
    (∃ n, a+6 = C 0 n) := by
  have hue : U a 3 = (2, a+6) := by simp [U]
  rw [hue]
  simp only [Prod.fst, Prod.snd]
  constructor
  · rintro ⟨steps,hs⟩
    exact even_trace_from_two_iff steps (a+6) hs
  · rintro ⟨n,heq⟩
    have hbase : EvenHalts (E 0) (C 0 n) :=
      (even_funnel_iff 0 (C 0 n)).mpr ⟨n, rfl⟩
    obtain ⟨steps,ht⟩ := even_funnel_trace (E 0) (C 0 n) hbase
    exact ⟨steps, by simpa [E, heq] using ht⟩

/-- Equivalent closed-form arithmetic target for a clean halt after c=3. -/
theorem U_three_closed_iff (a : Nat) :
    (∃ steps, EvenHIn steps (U a 3).1 (U a 3).2) ↔
    (∃ n, a+2*n+16 = 14*2^n) := by
  rw [U_three_clean_halt_iff]
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n, ?_⟩
    have hc := C_closed 0 n
    simp only [Nat.pow_zero, Nat.mul_one, Nat.zero_add] at hc
    omega
  · rintro ⟨n,hn⟩
    refine ⟨n, ?_⟩
    have hc := C_closed 0 n
    simp only [Nat.pow_zero, Nat.mul_one, Nat.zero_add] at hc
    omega

#print axioms BB6.HaltingFunnel.U_three_closed_iff
#print axioms BB6.HaltingFunnel.U_even_counter_iff_three
end BB6.HaltingFunnel
