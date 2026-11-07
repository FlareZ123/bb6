import SectionMassOriginal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3StrongMass
open BB6.Agent46 BB6.Agent8Section BB6.Agent11Mass

/-- Every successful bounce has strictly positive second output, including the c=4 exception. -/
theorem bounce_second_positive (c : Nat) : ∀ k x y : Nat,
    (bounce k c).2 = some (x,y) → 0 < y := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro k x y h
    rw [bounce.eq_1] at h
    by_cases hc : c < 4
    · simp [hc] at h
    simp only [hc, ite_false] at h
    by_cases hk : k%2=1
    · simp only [hk, ite_true] at h
      by_cases hs : c ≤ 2*k+6
      · simp only [hs, ite_true] at h
        cases h
        omega
      · simp only [hs, ite_false] at h
        exact ih _ (Nat.sub_lt (by omega) (by omega)) (2*k+3) x y h
    · simp only [hk, ite_false] at h
      by_cases h4 : c=4
      · simp [h4] at h
        cases h
        omega
      · simp only [h4, ite_false] at h
        by_cases h5 : c=5
        · simp [h5] at h
        · simp only [h5, ite_false] at h
          by_cases hs : c ≤ 2*k+8
          · simp only [hs, ite_true] at h
            cases h
            omega
          · simp only [hs, ite_false] at h
            exact ih _ (Nat.sub_lt (by omega) (by omega)) (2*k+4) x y h

/-- The source section never returns a state with zero second counter. -/
theorem secNext_second_positive (a k x y : Nat)
    (h : secNext (a,k) = some (x,y)) : 0 < y := by
  change (exactSection (a,k)).2=some (x,y) at h
  unfold exactSection at h
  by_cases ha0 : a=0
  · simp only [ha0,ite_true] at h
    by_cases hk0 : k=0
    · simp [hk0] at h
    · simp only [hk0,ite_false] at h
      by_cases hk1 : k=1
      · simp [hk1] at h
        cases h
        omega
      · simp only [hk1,ite_false] at h
        exact bounce_second_positive (2*k+1) 1 x y h
  · simp only [ha0,ite_false] at h
    by_cases ha1 : a=1
    · simp only [ha1,ite_true] at h
      by_cases hk0 : k=0
      · simp [hk0] at h
        cases h
        omega
      · simp only [hk0,ite_false] at h
        by_cases hk1 : k=1
        · simp [hk1] at h
          cases h
          omega
        · simp only [hk1,ite_false] at h
          by_cases hk2 : k=2
          · simp [hk2] at h
            cases h
            omega
          · simp only [hk2,ite_false] at h
            by_cases hk3 : k=3
            · simp [hk3] at h
              cases h
              omega
            · simp only [hk3,ite_false] at h
              exact bounce_second_positive (2*k-3) 4 x y h
    · simp only [ha1,ite_false] at h
      by_cases hk0 : k=0
      · simp [hk0] at h
        cases h
        omega
      · simp only [hk0,ite_false] at h
        by_cases hregion : 2*k≤a
        · simp [hregion] at h
          cases h
          omega
        · simp only [hregion,ite_false] at h
          exact bounce_second_positive (2*k-a+3) (a-1) x y h

/-- Every positive-second-counter section step grows mass by four or more. -/
theorem secNext_weight_growth_four (a k x y : Nat)
    (hk : 0 < k)
    (h : secNext (a,k) = some (x,y)) : a+2*k+4 ≤ x+2*y := by
  change (exactSection (a,k)).2 = some (x,y) at h
  unfold exactSection at h
  by_cases ha0 : a=0
  · simp only [ha0,ite_true] at h
    by_cases hk1 : k=1
    · simp [hk1] at h
      cases h
      omega
    · have hk0 : k≠0 := by omega
      simp only [hk0,ite_false,hk1] at h
      have hb := bounce_weight_growth (2*k+1) 1 x y h
      omega
  · simp only [ha0,ite_false] at h
    by_cases ha1 : a=1
    · simp only [ha1,ite_true] at h
      by_cases hk1 : k=1
      · simp [hk1] at h
        cases h
        omega
      · have hk0 : k≠0 := by omega
        simp only [hk0,ite_false,hk1] at h
        by_cases hk2 : k=2
        · simp [hk2] at h
          cases h
          omega
        · simp only [hk2,ite_false] at h
          by_cases hk3 : k=3
          · simp [hk3] at h
            cases h
            omega
          · simp only [hk3,ite_false] at h
            have hb := bounce_weight_growth (2*k-3) 4 x y h
            omega
    · simp only [ha1,ite_false] at h
      have hk0 : k≠0 := by omega
      simp only [hk0,ite_false] at h
      by_cases hregion : 2*k≤a
      · simp only [hregion,ite_true] at h
        cases h
        omega
      · simp only [hregion,ite_false] at h
        have hb := bounce_weight_growth (2*k-a+3) (a-1) x y h
        omega

/-- Real blank-origin section steps grow mass at least four each. -/
theorem blank_run_quad_mass (n : Nat) : ∀ x y : Nat,
    run secNext n (some (5,1)) = some (x,y) →
    0 < y ∧ 7 + 4*n ≤ x+2*y := by
  induction n with
  | zero =>
    intro x y h
    simp only [run] at h
    cases h
    omega
  | succ n ih =>
    intro x y h
    change (run secNext n (some (5,1))).bind secNext=some (x,y) at h
    cases hp : run secNext n (some (5,1)) with
    | none => simp [hp] at h
    | some p =>
      rcases p with ⟨a,k⟩
      obtain ⟨hk,hm⟩ := ih a k hp
      simp only [hp,Option.bind_some] at h
      have h1 := secNext_second_positive a k x y h
      have h2 := secNext_weight_growth_four a k x y hk h
      exact ⟨h1, by omega⟩

/-- Four-unit mass increase yields a source-exact quarter-fuel reachability bound. -/
theorem section_reach_iff_quarter_bound (x y : Nat) :
    SectionReach x y ↔ ∃ n ≤ (x+2*y-7)/4,
      run secNext n (some (5,1)) = some (x,y) := by
  constructor
  · rintro ⟨n,hn⟩
    have hm := (blank_run_quad_mass n x y hn).2
    exact ⟨n, by omega, hn⟩
  · rintro ⟨n,_,hn⟩
    exact ⟨n,hn⟩

#print axioms secNext_second_positive
#print axioms secNext_weight_growth_four
#print axioms blank_run_quad_mass
#print axioms section_reach_iff_quarter_bound
end BB6.Agent3StrongMass
