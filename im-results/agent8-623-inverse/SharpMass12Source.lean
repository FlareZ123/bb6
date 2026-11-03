import Agent8SharpMass10Source

/-! A strengthened twelve-unit mass budget for every surviving #623 section
with even a >= 6 and d > 0. -/
namespace BB6.Agent8SharpSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
private abbrev next : HighLevelState → Option HighLevelState := highLevelNext

theorem evalA_mass_zero_q2 (a k m aa dd : Nat)
    (ha : 0<a) (hq : 2≤k/3)
    (h : evalA a k m = some (aa,0,dd)) :
    a+m+6≤aa+dd := by
  rw [evalA] at h
  have hn : a≠0 := by omega
  by_cases hk2 : k%3=2
  · simp only [if_pos hk2] at h
    simp only [Option.some.injEq,Prod.mk.injEq] at h
    omega
  · simp only [if_neg hk2,if_neg hn] at h
    by_cases hk0 : k%3=0
    · simp only [if_pos hk0] at h
      simp only [Option.some.injEq,Prod.mk.injEq] at h
      omega
    · simp only [if_neg hk0] at h
      have hm:=evalA_mass (a-1) (k/3) (m+2*(k/3)+3) aa 0 dd h
      omega

theorem evalA_mass_zero_odd3 (a k m aa dd : Nat)
    (ha : 0<a) (hodd : k%2=1) (hk : 3≤k)
    (h : evalA a k m = some (aa,0,dd)) :
    a+m+6≤aa+dd := by
  by_cases hq : 2≤k/3
  · exact evalA_mass_zero_q2 a k m aa dd ha hq h
  · have hk0 : k%3=0 ∨ k%3=2 := by omega
    rw [evalA] at h
    have hn : a ≠ 0 := by omega
    rcases hk0 with hz | hz
    · have hk2 : k%3≠2 := by omega
      simp only [if_neg hk2,if_neg hn,if_pos hz] at h
      simp only [Option.some.injEq,Prod.mk.injEq] at h
      omega
    · simp only [if_pos hz] at h
      simp only [Option.some.injEq,Prod.mk.injEq] at h
      omega

theorem evalA_mass_zero_even6 (a k m aa dd : Nat)
    (ha : 0<a) (heven : k%2=0) (hk : 6≤k)
    (h : evalA a k m = some (aa,0,dd)) :
    a+m+6≤aa+dd := by
  have hq : 2≤k/3 := by omega
  exact evalA_mass_zero_q2 a k m aa dd ha hq h

theorem evalA_zero_odd_bpos (k m aa bb dd : Nat)
    (hk : 3≤k) (hodd : k%2=1)
    (h : evalA 0 k m = some (aa,bb,dd)) : 0<bb := by
  rw [evalA] at h
  by_cases hk2 : k%3=2
  · simp only [if_pos hk2] at h
    cases h
    omega
  · simp only [if_neg hk2, if_pos (by decide : (0:Nat)=0)] at h
    by_cases hk0 : k%3=0
    · simp [hk0] at h
    · simp only [if_neg hk0] at h
      cases h
      omega

/-- Even b>=4 with positive first counter has nine-unit B-drain surplus. -/
theorem drainB_mass_even_big_pos (b : Nat) (hb : 4≤b)
    (hbeven : b%2=0) (a d aa dd : Nat) (ha : 0<a)
    (h : drainB a b d = some (.D aa dd)) :
    a+d+2*b+9 ≤ aa+dd := by
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
        have hm:=evalA_mass_zero_odd3 a (b-1) (d+2*b+3) a1 d1 ha (by omega) (by omega) he
        have hr:=(drainB_mass 0 a1 d1 aa dd h).1
        omega
      · have hm:=evalA_mass_odd a (b-1) (d+2*b+3) a1 b1 d1 ha (by omega) he
        have hr:=(drainB_mass b1 a1 d1 aa dd h).2 (by omega)
        omega
    · simp [hlt] at h

/-- Even b>=4 at a=0 has eight-unit B-drain surplus. -/
theorem drainB_mass_even_big_zero (b : Nat) (hb : 4≤b)
    (hbeven : b%2=0) (d aa dd : Nat)
    (h : drainB 0 b d = some (.D aa dd)) :
    d+2*b+8 ≤ aa+dd := by
  rw [drainB] at h
  simp only [if_neg (by omega : b≠0)] at h
  cases he : evalA 0 (b-1) (d+2*b+3) with
  | none => simp [he] at h
  | some p =>
    rcases p with ⟨a1,b1,d1⟩
    simp only [he,Option.bind_some] at h
    by_cases hlt : b1<b
    · simp only [if_pos hlt] at h
      have hbpos:=evalA_zero_odd_bpos (b-1) (d+2*b+3) a1 b1 d1 (by omega) (by omega) he
      have hm:=evalA_zero_mass_large (b-1) (d+2*b+3) a1 b1 d1 (by omega) he
      have hr:=(drainB_mass b1 a1 d1 aa dd h).2 hbpos
      omega
    · simp [hlt] at h

/-- Odd b>=5 and positive first counter have seven surplus mass units. -/
theorem drainB_mass_odd_big_pos (b : Nat) (hb : 5≤b)
    (hodd : b%2=1) (a d aa dd : Nat) (ha : 0<a)
    (h : drainB a b d = some (.D aa dd)) :
    a+d+2*b+7 ≤ aa+dd := by
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
        have hm:=evalA_mass_zero_large a (b-1) (d+2*b+3) a1 d1 ha (by omega) he
        have hr:=(drainB_mass 0 a1 d1 aa dd h).1
        omega
      · have hm:=evalA_mass_even_large a (b-1) (d+2*b+3) a1 b1 d1 ha (by omega) (by omega) he
        have hr:=(drainB_mass b1 a1 d1 aa dd h).2 (by omega)
        omega
    · simp [hlt] at h

/-- All successful transitions with even a>=6 and positive d gain twelve. -/
theorem next_even_six_positive_d_mass (a d aa dd : Nat)
    (heven : a%2=0) (hlarge : 6≤a) (hdpos : 0<d)
    (hstep : next (.D a d) = some (.D aa dd)) :
    a+d+12 ≤ aa+dd := by
  simp only [next, highLevelNext] at hstep
  have hn : a≠0 := by omega
  simp only [if_neg hn] at hstep
  by_cases h1 : d%2=1 ∧ a≥d+5
  · simp only [if_pos h1] at hstep
    by_cases ha : a-d-5=0
    · have hm:=drainB_mass_even_big_zero (d+3) (by omega) (by omega) 5 aa dd
        (by simpa only [ha] using hstep)
      omega
    · have hm:=drainB_mass_even_big_pos (d+3) (by omega) (by omega)
        (a-d-5) 5 aa dd (by omega) hstep
      omega
  · simp only [if_neg h1] at hstep
    by_cases h2 : d%2=0 ∧ a≥d+3
    · simp only [if_pos h2] at hstep
      have hm:=drainB_mass_even_big_pos (d+2) (by omega) (by omega)
        (a-d-2) 2 aa dd (by omega) hstep
      omega
    · simp only [if_neg h2] at hstep
      have hpar : a%2≠1 := by omega
      simp only [if_neg hpar] at hstep
      by_cases h4 : a=d+2
      · simp only [if_pos h4] at hstep
        by_cases ha8 : 8≤a
        · have hm:=BB6.Agent8BudgetSource.drainB_d3 a 0 2 aa dd hstep
          omega
        · have ha6 : a=6 := by omega
          have hd4 : d=4 := by omega
          subst a
          subst d
          have heq : drainB 0 6 2 = some (.D 0 24) := by decide +kernel
          rw [heq] at hstep
          cases hstep
          omega
      · simp only [if_neg h4] at hstep
        by_cases h5 : d%2=1
        · simp only [if_pos h5] at hstep
          have hm:=drainB_mass_odd_big_pos (a-1) (by omega) (by omega)
            (d+4-a) 3 aa dd (by omega) hstep
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
              have hm:=evalA_mass_zero_even6 (d+1-a) a (2*a+5) p1 p3 ha heven (by omega) he
              have hr:=(drainB_mass 0 p1 p3 aa dd hstep).1
              omega
            · have hm:=evalA_mass_even_large (d+1-a) a (2*a+5) p1 p2 p3 ha heven (by omega) he
              have hr:=(drainB_mass p2 p1 p3 aa dd hstep).2 (by omega)
              omega

#print axioms next_even_six_positive_d_mass
end BB6.Agent8SharpSource
