import Agent8SharpMass14AuxSource
namespace BB6.Agent8SharpSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
private abbrev next : HighLevelState → Option HighLevelState := highLevelNext

theorem evalA_mass_zero_even8 (a k m aa dd : Nat)
    (ha : 0<a) (heven : k%2=0) (hk : 6≤k)
    (h : evalA a k m = some (aa,0,dd)) :
    a+m+8 ≤ aa+dd := by
  rw [evalA] at h
  have hn : a≠0 := by omega
  by_cases h2 : k%3=2
  · simp only [if_pos h2] at h
    simp only [Option.some.injEq,Prod.mk.injEq] at h
    omega
  · simp only [if_neg h2,if_neg hn] at h
    by_cases h0 : k%3=0
    · simp only [if_pos h0] at h
      simp only [Option.some.injEq,Prod.mk.injEq] at h
      omega
    · simp only [if_neg h0] at h
      have hq : 3≤k/3 := by omega
      have hm:=evalA_mass_nontrivial (a-1) (k/3) (m+2*(k/3)+3) aa 0 dd (by omega) h
      omega

/-- Every successful step with a even >=6 and d positive even gains >=14. -/
theorem next_even_six_even_d_mass14 (a d aa dd : Nat)
    (heven : a%2=0) (hlarge : 6≤a) (hdpos : 0<d)
    (hdeven : d%2=0) (hstep : next (.D a d) = some (.D aa dd)) :
    a+d+14 ≤ aa+dd := by
  simp only [next,highLevelNext] at hstep
  have hn : a≠0 := by omega
  simp only [if_neg hn] at hstep
  have h1 : ¬ (d%2=1 ∧ a≥d+5) := by omega
  simp only [if_neg h1] at hstep
  by_cases h2 : d%2=0 ∧ a≥d+3
  · simp only [if_pos h2] at hstep
    have hm:=drainB_mass_even_big_pos10 (d+2) (by omega) (by omega)
      (a-d-2) 2 aa dd (by omega) hstep
    omega
  · simp only [if_neg h2] at hstep
    have hp : a%2≠1 := by omega
    simp only [if_neg hp] at hstep
    by_cases h4 : a=d+2
    · simp only [if_pos h4] at hstep
      by_cases ha10 : 10≤a
      · have hm:=BB6.Agent8BudgetSource.drainB_d3 a 0 2 aa dd hstep
        omega
      · have h68 : a=6 ∨ a=8 := by omega
        rcases h68 with h6 | h8
        · have hd4 : d=4 := by omega
          subst a
          subst d
          have he : drainB 0 6 2 = some (.D 0 24) := by decide +kernel
          rw [he] at hstep
          cases hstep
          omega
        · have hd6 : d=6 := by omega
          subst a
          subst d
          have he : drainB 0 8 2 = some (.D 0 28) := by decide +kernel
          rw [he] at hstep
          cases hstep
          omega
    · simp only [if_neg h4] at hstep
      have h5 : d%2≠1 := by omega
      simp only [if_neg h5] at hstep
      cases he : evalA (d+1-a) a (2*a+5) with
      | none => simp [he] at hstep
      | some p =>
        rcases p with ⟨p1,p2,p3⟩
        simp only [he,Option.bind_some] at hstep
        have ha : 0<d+1-a := by omega
        by_cases hz : p2=0
        · subst p2
          have hm:=evalA_mass_zero_even8 (d+1-a) a (2*a+5) p1 p3 ha heven (by omega) he
          have hr:=(drainB_mass 0 p1 p3 aa dd hstep).1
          omega
        · have hm:=evalA_mass_even_large (d+1-a) a (2*a+5) p1 p2 p3 ha heven (by omega) he
          have hr:=drainB_mass_b5 p2 p1 p3 aa dd (by omega) hstep
          omega

#print axioms next_even_six_even_d_mass14
end BB6.Agent8SharpSource
