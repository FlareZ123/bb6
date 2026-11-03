import Agent8SharpMassSource

namespace BB6.Agent8SharpSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
private abbrev next : HighLevelState → Option HighLevelState := highLevelNext

/-- A successful evaluator at positive a and k>=3 cannot have both zero
residual blocks and mass increment under four. -/
theorem evalA_mass_zero_large (a k m aa dd : Nat)
    (ha : 0 < a) (hk : 3 ≤ k)
    (h : evalA a k m = some (aa,0,dd)) :
    a + m + 4 ≤ aa + dd := by
  rw [evalA] at h
  have hn : a ≠ 0 := by omega
  by_cases hk2 : k%3=2
  · simp only [if_pos hk2] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    omega
  · simp only [if_neg hk2, if_neg hn] at h
    by_cases hk0 : k%3=0
    · simp only [if_pos hk0] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      omega
    · simp only [if_neg hk0] at h
      have hm := evalA_mass (a-1) (k/3) (m+2*(k/3)+3) aa 0 dd h
      omega

/-- A successful zero-first-counter evaluator with k>=3 gains a positive
quantity in a + b + m. -/
theorem evalA_zero_mass_large (k m aa bb dd : Nat)
    (hk : 3 ≤ k) (h : evalA 0 k m = some (aa,bb,dd)) :
    m+1 ≤ aa+bb+dd := by
  rw [evalA] at h
  by_cases hk2 : k%3=2
  · simp only [if_pos hk2] at h
    cases h
    omega
  · simp only [if_neg hk2, if_pos (by decide : (0:Nat)=0)] at h
    by_cases hk0 : k%3=0
    · simp only [if_pos hk0] at h
      contradiction
    · simp only [if_neg hk0] at h
      cases h
      omega

/-- When k is odd, a zero-residual successful evaluation gains three. -/
theorem evalA_mass_odd_zero (a k m aa dd : Nat)
    (ha : 0<a) (hodd : k%2=1)
    (h : evalA a k m = some (aa,0,dd)) :
    a+m+3 ≤ aa+dd := by
  by_cases hk : 3 ≤ k
  · have hg := evalA_mass_zero_large a k m aa dd ha hk h
    omega
  · have hk1 : k=1 := by omega
    subst k
    rw [evalA] at h
    simp only [if_neg (by decide : 1%3 ≠ 2), if_neg (by omega : a ≠ 0),
      if_neg (by decide : 1%3 ≠ 0)] at h
    by_cases ha1 : a=1
    · subst a
      simp [evalA] at h
    · have hpos : 0<a-1 := by omega
      have hm := evalA_mass_positive (a-1) 0 (m+3) aa 0 dd hpos h
      omega

/-- Large positive-index B-drain gains four units beyond initial baseline. -/
theorem drainB_mass_large (b : Nat) (hb : 4 ≤ b) (a d aa dd : Nat)
    (h : drainB a b d = some (.D aa dd)) :
    a+d+2*b+4 ≤ aa+dd := by
  rw [drainB] at h
  simp only [if_neg (by omega : b≠0)] at h
  cases he : evalA a (b-1) (d+2*b+3) with
  | none => simp [he] at h
  | some p =>
    rcases p with ⟨a1,b1,d1⟩
    simp only [he,Option.bind_some] at h
    by_cases hlt : b1 < b
    · simp only [if_pos hlt] at h
      have hm : a+(d+2*b+3)+1 ≤ a1+b1+d1 := by
        by_cases ha : a=0
        · subst a
          have hg := evalA_zero_mass_large (b-1) (d+2*b+3) a1 b1 d1
            (by omega) he
          omega
        · have hg := evalA_mass_positive a (b-1) (d+2*b+3) a1 b1 d1 (by omega) he
          omega
      have hr := (drainB_mass b1 a1 d1 aa dd h).1
      omega
    · simp [hlt] at h

/-- Positive first counter, even block count: three or more units of mass
beyond the first B-drain base budget. -/
theorem drainB_mass_even (b : Nat) (hb : 0<b) (hbeven : b%2=0)
    (a d aa dd : Nat) (ha : 0<a)
    (h : drainB a b d = some (.D aa dd)) :
    a+d+2*b+6 ≤ aa+dd := by
  rw [drainB] at h
  simp only [if_neg (by omega : b≠0)] at h
  cases he : evalA a (b-1) (d+2*b+3) with
  | none => simp [he] at h
  | some p =>
    rcases p with ⟨a1,b1,d1⟩
    simp only [he,Option.bind_some] at h
    by_cases hlt : b1<b
    · simp only [if_pos hlt] at h
      by_cases hz : b1=0
      · subst b1
        have hm := evalA_mass_odd_zero a (b-1) (d+2*b+3) a1 d1 ha (by omega) he
        have hr := (drainB_mass 0 a1 d1 aa dd h).1
        omega
      · have hm := evalA_mass_odd a (b-1) (d+2*b+3) a1 b1 d1 ha (by omega) he
        have hr := (drainB_mass b1 a1 d1 aa dd h).2 (by omega)
        omega
    · simp [hlt] at h

/-- An odd B-drain block count at least five starts with an even index
at least four, giving a three-unit first-evaluator mass surplus. -/
theorem drainB_mass_odd_large (b : Nat) (hb : 5 ≤ b)
    (hodd : b%2=1) (a d aa dd : Nat) (ha : 0<a)
    (h : drainB a b d = some (.D aa dd)) :
    a+d+2*b+6 ≤ aa+dd := by
  rw [drainB] at h
  simp only [if_neg (by omega : b ≠ 0)] at h
  cases he : evalA a (b-1) (d+2*b+3) with
  | none => simp [he] at h
  | some p =>
    rcases p with ⟨a1,b1,d1⟩
    simp only [he,Option.bind_some] at h
    by_cases hlt : b1<b
    · simp only [if_pos hlt] at h
      have hm := evalA_mass_even_large a (b-1) (d+2*b+3) a1 b1 d1
        ha (by omega) (by omega) he
      have hr := (drainB_mass b1 a1 d1 aa dd h).1
      omega
    · simp [hlt] at h

/-- Source-matched universal ten-unit gain for successful even-a>=6 steps. -/
theorem next_even_six_mass (a d aa dd : Nat)
    (heven : a%2=0) (hlarge : 6≤a)
    (hstep : next (.D a d) = some (.D aa dd)) :
    a+d+10 ≤ aa+dd := by
  simp only [next,highLevelNext] at hstep
  have hn : a ≠ 0 := by omega
  simp only [if_neg hn] at hstep
  by_cases h1 : d%2=1 ∧ a≥d+5
  · simp only [if_pos h1] at hstep
    have hm := drainB_mass_large (d+3) (by omega) (a-d-5) 5 aa dd hstep
    omega
  · simp only [if_neg h1] at hstep
    by_cases h2 : d%2=0 ∧ a≥d+3
    · simp only [if_pos h2] at hstep
      have hm := drainB_mass_even (d+2) (by omega) (by omega)
        (a-d-2) 2 aa dd (by omega) hstep
      omega
    · simp only [if_neg h2] at hstep
      have hpar : a%2 ≠ 1 := by omega
      simp only [if_neg hpar] at hstep
      by_cases h4 : a=d+2
      · simp only [if_pos h4] at hstep
        have hm := BB6.Agent8BudgetSource.drainB_d3 a 0 2 aa dd hstep
        omega
      · simp only [if_neg h4] at hstep
        by_cases h5 : d%2=1
        · simp only [if_pos h5] at hstep
          have hm := drainB_mass_odd_large (a-1) (by omega) (by omega) (d+4-a) 3 aa dd (by omega) hstep
          omega
        · simp only [if_neg h5] at hstep
          cases he : evalA (d+1-a) a (2*a+5) with
          | none => simp [he] at hstep
          | some p =>
            rcases p with ⟨p1,p2,p3⟩
            simp only [he,Option.bind_some] at hstep
            have ha : 0<d+1-a := by omega
            by_cases hz : p2=0
            · subst p2
              have hm := evalA_mass_zero_large (d+1-a) a (2*a+5) p1 p3 ha (by omega) he
              have hr := (drainB_mass 0 p1 p3 aa dd hstep).1
              omega
            · have hm := evalA_mass_even_large (d+1-a) a (2*a+5) p1 p2 p3 ha heven (by omega) he
              have hr := (drainB_mass p2 p1 p3 aa dd hstep).2 (by omega)
              omega

#print axioms next_even_six_mass
end BB6.Agent8SharpSource
