import Agent49ParitySource
import Agent8BudgetSource

/-! Sharpened mass-growth theorem over the unmodified BB6 #623 source.
The supporting mass and ternary-budget facts are reused from the
original-source Agent49 and Agent8 proof modules. -/
namespace BB6.Agent8SharpSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
private abbrev next : HighLevelState → Option HighLevelState := highLevelNext

/-- A positive evaluator first counter and odd block index yield two units
of surplus in the weighted mass inequality. -/
theorem evalA_mass_odd (a k m aa bb dd : Nat)
    (ha : 0 < a) (hk : k % 2 = 1)
    (h : evalA a k m = some (aa, bb, dd)) :
    a + m + 2 ≤ aa + bb + dd := by
  rw [evalA] at h
  have hn : a ≠ 0 := by omega
  by_cases hk2 : k % 3 = 2
  · simp only [if_pos hk2] at h
    cases h
    omega
  · simp only [if_neg hk2, if_neg hn] at h
    by_cases hk0 : k % 3 = 0
    · simp only [if_pos hk0] at h
      cases h
      omega
    · simp only [if_neg hk0] at h
      have hm := evalA_mass (a - 1) (k / 3) (m + 2 * (k / 3) + 3) aa bb dd h
      omega

/-- Even evaluator indices at least four give three surplus units. -/
theorem evalA_mass_even_large (a k m aa bb dd : Nat)
    (ha : 0 < a) (hk : k % 2 = 0) (hlarge : 4 ≤ k)
    (h : evalA a k m = some (aa, bb, dd)) :
    a + m + 3 ≤ aa + bb + dd := by
  rw [evalA] at h
  have hn : a ≠ 0 := by omega
  by_cases hk2 : k % 3 = 2
  · simp only [if_pos hk2] at h
    cases h
    omega
  · simp only [if_neg hk2, if_neg hn] at h
    by_cases hk0 : k % 3 = 0
    · simp only [if_pos hk0] at h
      cases h
      omega
    · simp only [if_neg hk0] at h
      have hm := evalA_mass (a - 1) (k / 3) (m + 2 * (k / 3) + 3) aa bb dd h
      omega

/-- A positive initial B-drain first counter gives one further surplus. -/
theorem drainB_mass_pos (b : Nat) (hb : 0 < b) (a d aa dd : Nat)
    (ha : 0 < a) (h : drainB a b d = some (.D aa dd)) :
    a + d + 2*b + 4 ≤ aa + dd := by
  rw [drainB] at h
  simp only [if_neg (by omega : b ≠ 0)] at h
  cases he : evalA a (b - 1) (d + 2*b + 3) with
  | none => simp [he] at h
  | some p =>
    rcases p with ⟨a1,b1,d1⟩
    simp only [he,Option.bind_some] at h
    by_cases hlt : b1 < b
    · simp only [if_pos hlt] at h
      have hm := evalA_mass_positive a (b-1) (d+2*b+3) a1 b1 d1 ha he
      have hr := (drainB_mass b1 a1 d1 aa dd h).1
      omega
    · simp [hlt] at h

/-- A positive B-drain first counter and odd first index gain two units. -/
theorem drainB_mass_odd_first (b : Nat) (hb : 0 < b) (a d aa dd : Nat)
    (ha : 0 < a) (hodd : (b-1)%2 = 1)
    (h : drainB a b d = some (.D aa dd)) :
    a + d + 2*b + 5 ≤ aa + dd := by
  rw [drainB] at h
  simp only [if_neg (by omega : b ≠ 0)] at h
  cases he : evalA a (b-1) (d+2*b+3) with
  | none => simp [he] at h
  | some p =>
    rcases p with ⟨a1,b1,d1⟩
    simp only [he,Option.bind_some] at h
    by_cases hlt : b1 < b
    · simp only [if_pos hlt] at h
      have hm := evalA_mass_odd a (b-1) (d+2*b+3) a1 b1 d1 ha hodd he
      have hr := (drainB_mass b1 a1 d1 aa dd h).1
      omega
    · simp [hlt] at h

/-- Every successful #623 high-level step starting with even a >=4
increases a+d by at least nine. -/
theorem next_even_large_mass (a d aa dd : Nat)
    (heven : a % 2 = 0) (hlarge : 4 ≤ a)
    (hstep : next (.D a d) = some (.D aa dd)) :
    a+d+9 ≤ aa+dd := by
  simp only [next, highLevelNext] at hstep
  have hn : a ≠ 0 := by omega
  simp only [if_neg hn] at hstep
  by_cases h1 : d % 2 = 1 ∧ a ≥ d+5
  · simp only [if_pos h1] at hstep
    have hm := drainB_mass (d+3) (a-d-5) 5 aa dd hstep
    omega
  · simp only [if_neg h1] at hstep
    by_cases h2 : d % 2 = 0 ∧ a ≥ d+3
    · simp only [if_pos h2] at hstep
      have hb : 0 < d+2 := by omega
      have ha : 0 < a-d-2 := by omega
      have hodd : ((d+2)-1)%2=1 := by omega
      have hm := drainB_mass_odd_first (d+2) hb (a-d-2) 2 aa dd ha hodd hstep
      omega
    · simp only [if_neg h2] at hstep
      have hpar : a%2≠1 := by omega
      simp only [if_neg hpar] at hstep
      by_cases h4 : a=d+2
      · simp only [if_pos h4] at hstep
        by_cases hgt : 6 ≤ a
        · have hd := BB6.Agent8BudgetSource.drainB_d3 a 0 2 aa dd hstep
          omega
        · have heq : a = 4 := by omega
          have hd_eq : d = 2 := by omega
          subst a
          subst d
          have hno : drainB 0 4 2 = none := by decide +kernel
          simp [hno] at hstep
      · simp only [if_neg h4] at hstep
        by_cases h5 : d%2=1
        · simp only [if_pos h5] at hstep
          have ha : 0 < d+4-a := by omega
          have hb : 0 < a-1 := by omega
          have hm := drainB_mass_pos (a-1) hb (d+4-a) 3 aa dd ha hstep
          omega
        · simp only [if_neg h5] at hstep
          cases he : evalA (d+1-a) a (2*a+5) with
          | none => simp [he] at hstep
          | some p =>
            rcases p with ⟨p1,p2,p3⟩
            simp only [he,Option.bind_some] at hstep
            have ha : 0 < d+1-a := by omega
            have hm := evalA_mass_even_large (d+1-a) a (2*a+5) p1 p2 p3 ha heven hlarge he
            have hr := (drainB_mass p2 p1 p3 aa dd hstep).1
            omega

#print axioms next_even_large_mass
end BB6.Agent8SharpSource
