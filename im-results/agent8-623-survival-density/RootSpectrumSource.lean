import Agent8BudgetSource
import Agent49ParitySource

/-!
Original-source theorem for the #623 high-level blank-root orbit:
for every surviving return, third counter d belongs to
{7,9,10,12,14} ∪ [23,∞). Derived from exact small-counter branches,
all-input original drain growth, and original parity theorem.
The conclusion is necessary and does not prove never-halting.
-/
namespace BB6.Agent8RootSpectrumSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent8BudgetSource

theorem evalA_third_ge (a : Nat) :
    ∀ k m aa bb dd : Nat, evalA a k m = some (aa,bb,dd) → m ≤ dd := by
  induction a with
  | zero =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3=2
    · simp only [if_pos h2] at h
      cases h
      omega
    · simp only [if_neg h2] at h
      by_cases h0 : k%3=0
      · simp [h0] at h
      · simp [h0] at h
        cases h
        omega
  | succ a ih =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3=2
    · simp only [if_pos h2] at h
      cases h
      omega
    · simp only [if_neg h2] at h
      have ha : a+1 ≠ 0 := by omega
      simp only [if_neg ha] at h
      by_cases h0 : k%3=0
      · simp only [if_pos h0] at h
        cases h
        omega
      · simp only [if_neg h0] at h
        have hi := ih (k/3) (m+2*(k/3)+3) aa bb dd h
        omega

-- Need exact a=0 odd output; this is direct constant-sized drain.
theorem axis_odd_exact (d : Nat) (hd : d%2=1) :
    highLevelNext (.D 0 d) = some (.D (d-1) 14) := by
  rw [highLevelNext]
  simp only [if_pos (by decide : (0:Nat)=0), if_pos hd]
  have hd1 : d+1≠0 := by omega
  rw [drainB]
  simp only [if_neg (by decide : (2:Nat)≠0)]
  have hdpos : d≠0 := by omega
  have h1 : evalA (d+1) 1 9 = evalA d 0 12 := by
    rw [evalA]
    simp only [if_neg (by decide : 1%3≠2),if_neg hd1,
      if_neg (by decide : 1%3≠0)]
    have h : d+1-1=d := by omega
    simp only [h]
  have he1 : evalA (d+1) 1 9 = some (d-1,0,14) := by
    rw [h1, evalA]
    simp [hdpos]
  rw [he1]
  simp only [Option.bind_some, if_pos (by decide : (0:Nat)<2)]
  rw [drainB]
  simp


theorem drainB_one_exact (x d : Nat) (hx : 0 < x) :
    drainB x 1 d = some (.D (x-1) (d+7)) := by
  rw [drainB]
  simp only [if_neg (by decide : (1:Nat)≠0)]
  have hn : x≠0 := by omega
  have he : evalA x 0 (d+5) = some (x-1,0,d+7) := by
    rw [evalA]
    simp [hn]
  rw [he]
  simp only [Option.bind_some,if_pos (by decide : (0:Nat)<1)]
  rw [drainB]
  simp

/-- Every surviving even-first-counter step from a positive counter and
third coordinate >=7 lands at third coordinate >=9. -/
theorem next_positive_third_ge_nine (a d aa dd : Nat)
    (ha : a%2=0) (hap : 0<a) (hd : 7≤d)
    (h : highLevelNext (.D a d) = some (.D aa dd)) : 9≤dd := by
  have ha0 : a≠0 := by omega
  simp only [highLevelNext,if_neg ha0] at h
  by_cases hl1 : d%2=1 ∧ a≥d+5
  · simp only [if_pos hl1] at h
    have hbound := drainB_d3 (d+3) (a-d-5) 5 aa dd h
    omega
  · simp only [if_neg hl1] at h
    by_cases hl2 : d%2=0 ∧ a≥d+3
    · simp only [if_pos hl2] at h
      have hbound := drainB_d3 (d+2) (a-d-2) 2 aa dd h
      omega
    · simp only [if_neg hl2] at h
      have hae : a%2≠1 := by omega
      simp only [if_neg hae] at h
      by_cases hdiag : a=d+2
      · simp only [if_pos hdiag] at h
        have hbound := drainB_d3 a 0 2 aa dd h
        omega
      · simp only [if_neg hdiag] at h
        by_cases hodd : d%2=1
        · simp only [if_pos hodd] at h
          by_cases ha2 : a=2
          · have hb : drainB (d+4-a) (a-1) 3 = some (.D (d+1) 10) := by
              have hxp : 0<d+4-a := by omega
              have hq : a-1=1 := by omega
              rw [hq,drainB_one_exact (d+4-a) 3 hxp]
              have heq : d+4-a-1=d+1 := by omega
              simp [heq]
            rw [hb] at h
            cases h
            omega
          · have hbound := drainB_d3 (a-1) (d+4-a) 3 aa dd h
            omega
        · simp only [if_neg hodd] at h
          cases hev : evalA (d+1-a) a (2*a+5) with
          | none => simp [hev] at h
          | some p =>
            rcases p with ⟨x,b,m⟩
            simp only [hev,Option.bind_some] at h
            have hege := evalA_third_ge (d+1-a) a (2*a+5) x b m hev
            have hbound := drainB_d3 b x m aa dd h
            omega

/-- All surviving even-root-compatible section states retain the strip d>=7. -/
theorem next_even_third_ge_seven (a d aa dd : Nat)
    (ha : a%2=0) (hd : 7≤d)
    (h : highLevelNext (.D a d) = some (.D aa dd)) : 7≤dd := by
  by_cases hz : a=0
  · subst a
    by_cases hodd : d%2=1
    · rw [axis_odd_exact d hodd] at h
      cases h
      omega
    · have heven : d%2=0 := by omega
      simp [highLevelNext,heven] at h
      cases h
      omega
  · have hh := next_positive_third_ge_nine a d aa dd ha (by omega) hd h
    omega

/-- Thus d'=8 is impossible on the entire forward-invariant even strip. -/
theorem next_forbids_eight (a d aa : Nat)
    (ha : a%2=0) (hd : 7≤d) :
    highLevelNext (.D a d) ≠ some (.D aa 8) := by
  intro h
  have ht := next_even_third_ge_seven a d aa 8 ha hd h
  by_cases hz : a=0
  · subst a
    by_cases hodd : d%2=1
    · rw [axis_odd_exact d hodd] at h
      cases h
    · have heven : d%2=0 := by omega
      simp [highLevelNext,heven] at h
  · have h9 := next_positive_third_ge_nine a d aa 8 ha (by omega) hd h
    omega


/-- A short base-three drain family used to exclude all low third outputs. -/
theorem evalA_one_exact (x m : Nat) (hx : 2≤x) :
    evalA x 1 m = some (x-2,0,m+5) := by
  rw [evalA]
  have h0 : x≠0 := by omega
  simp only [if_neg (by decide : 1%3≠2),if_neg h0,
    if_neg (by decide : 1%3≠0)]
  have heq : x-1≠0 := by omega
  rw [evalA]
  simp [heq]
  simp only [Nat.sub_sub]

theorem drain_two_exact (x d : Nat) (hx : 2≤x) :
    drainB x 2 d = some (.D (x-2) (d+12)) := by
  rw [drainB]
  simp only [if_neg (by decide : (2:Nat)≠0)]
  have he : evalA x 1 (d+7) = some (x-2,0,d+12) := by
    simpa only [show d+7+5=d+12 by omega] using evalA_one_exact x (d+7) hx
  rw [he]
  simp only [Option.bind_some,if_pos (by decide : (0:Nat)<2)]
  rw [drainB]
  simp

theorem evalA_four_first (x m : Nat) (hx : 3≤x) :
    evalA x 4 m = some (x-3,0,m+10) := by
  rw [evalA]
  have hx0 : x≠0 := by omega
  simp only [if_neg (by decide : 4%3≠2),if_neg hx0,
    if_neg (by decide : 4%3≠0)]
  have hr : evalA (x-1) 1 (m+5) = some ((x-1)-2,0,m+5+5) :=
    evalA_one_exact (x-1) (m+5) (by omega)
  rw [hr]
  congr 1 <;> omega

theorem drain_five_exact (x d : Nat) (hx : 3≤x) :
    drainB x 5 d = some (.D (x-3) (d+23)) := by
  rw [drainB]
  simp only [if_neg (by decide : (5:Nat)≠0)]
  have he : evalA x 4 (d+13) = some (x-3,0,d+23) := by
    simpa only [show d+13+10=d+23 by omega] using evalA_four_first x (d+13) hx
  rw [he]
  simp only [Option.bind_some,if_pos (by decide : (0:Nat)<5)]
  rw [drainB]
  simp

theorem drain_seven_exact (x d : Nat) (hx : 3≤x) :
    drainB x 7 d = some (.D (x-3) (d+31)) := by
  rw [drainB]
  simp only [if_neg (by decide : (7:Nat)≠0)]
  have he : evalA x 6 (d+17) = some (x-1,2,d+19) := by
    rw [evalA]
    have h0 : x≠0 := by omega
    simp only [if_neg (by decide : 6%3≠2),if_neg h0,
      if_pos (by decide : 6%3=0)]
    congr 1 <;> omega
  rw [he]
  simp only [Option.bind_some,if_pos (by decide : (2:Nat)<7)]
  have hs := drain_two_exact (x-1) (d+19) (by omega)
  rw [hs]
  congr 1 <;> omega


/-- The special leading ternary-one digit at k=10 costs at least nine units
unless the zero-counter branch retains at least three blocks. -/
theorem evalA_ten_floor (x aa bb mm : Nat)
    (h : evalA x 10 25 = some (aa,bb,mm)) : 29 ≤ mm+3*bb := by
  rw [evalA] at h
  have h2 : 10%3≠2 := by decide
  simp only [if_neg h2] at h
  by_cases hx : x=0
  · simp only [if_pos hx] at h
    simp at h
    cases h
    omega
  · simp only [if_neg hx] at h
    have h0 : 10%3≠0 := by decide
    simp only [if_neg h0] at h
    have hh := evalA_third_ge (x-1) 3 34 aa bb mm (by simpa using h)
    omega

/-- At first coordinate ten or higher, all surviving compatible states
have output third counter at least twenty-nine. -/
theorem next_large_third_ge_29 (a d aa dd : Nat)
    (ha : a%2=0) (ha10 : 10≤a) (hd : 7≤d)
    (h : highLevelNext (.D a d) = some (.D aa dd)) : 29≤dd := by
  have hnon : a≠0 := by omega
  simp only [highLevelNext,if_neg hnon] at h
  by_cases hl1 : d%2=1 ∧ a≥d+5
  · simp only [if_pos hl1] at h
    have hb := drainB_d3 (d+3) (a-d-5) 5 aa dd h
    omega
  · simp only [if_neg hl1] at h
    by_cases hl2 : d%2=0 ∧ a≥d+3
    · simp only [if_pos hl2] at h
      have hb := drainB_d3 (d+2) (a-d-2) 2 aa dd h
      omega
    · simp only [if_neg hl2] at h
      have hnotodd : a%2≠1 := by omega
      simp only [if_neg hnotodd] at h
      by_cases hdiag : a=d+2
      · simp only [if_pos hdiag] at h
        have hb := drainB_d3 a 0 2 aa dd h
        omega
      · simp only [if_neg hdiag] at h
        by_cases hodd : d%2=1
        · simp only [if_pos hodd] at h
          have hb := drainB_d3 (a-1) (d+4-a) 3 aa dd h
          omega
        · simp only [if_neg hodd] at h
          cases he : evalA (d+1-a) a (2*a+5) with
          | none => simp [he] at h
          | some p =>
            rcases p with ⟨x,b,m⟩
            simp only [he,Option.bind_some] at h
            have hb := drainB_d3 b x m aa dd h
            by_cases hlarge : 12≤a
            · have hm := evalA_third_ge (d+1-a) a (2*a+5) x b m he
              omega
            · have ha10eq : a=10 := by omega
              subst a
              have hten : evalA (d+1-10) 10 25 = some (x,b,m) := by simpa using he
              have hfloor := evalA_ten_floor (d+1-10) x b m hten
              omega


theorem drain_three_exact (x d : Nat) :
    drainB x 3 d = some (.D (x+1) (d+9)) := by
  rw [drainB]
  simp only [if_neg (by decide : (3:Nat)≠0)]
  have he : evalA x 2 (d+9) = some (x+1,0,d+9) := by
    rw [evalA]
    simp
  rw [he]
  simp only [Option.bind_some,if_pos (by decide : (0:Nat)<3)]
  rw [drainB]
  simp

/-- Full small-first-counter source formulas for d>=7. -/
theorem next_two_odd (d : Nat) (hd : d%2=1) (h7 : 7≤d) :
    highLevelNext (.D 2 d) = some (.D (d+1) 10) := by
  simp only [highLevelNext,if_neg (by decide : (2:Nat)≠0)]
  have h1 : ¬ (d%2=1 ∧ (2:Nat)≥d+5) := by omega
  have h2 : ¬ (d%2=0 ∧ (2:Nat)≥d+3) := by omega
  have h4 : 2 ≠ d+2 := by omega
  simp only [if_neg h1,if_neg h2,if_neg (by decide : (2:Nat)%2≠1),
    if_neg h4,if_pos hd]
  have hx : d+4-2=d+2 := by omega
  rw [hx,drainB_one_exact (d+2) 3 (by omega)]
  congr 1 <;> omega

theorem next_two_even (d : Nat) (hd : d%2=0) (h7 : 7≤d) :
    highLevelNext (.D 2 d) = some (.D d 9) := by
  simp only [highLevelNext,if_neg (by decide : (2:Nat)≠0)]
  have h1 : ¬ (d%2=1 ∧ (2:Nat)≥d+5) := by omega
  have h2 : ¬ (d%2=0 ∧ (2:Nat)≥d+3) := by omega
  have h4 : 2 ≠ d+2 := by omega
  have hodd : d%2≠1 := by omega
  simp only [if_neg h1,if_neg h2,if_neg (by decide : (2:Nat)%2≠1),
    if_neg h4,if_neg hodd]
  have hev : evalA (d+1-2) 2 9 = some (d,0,9) := by
    rw [evalA]
    simp only [Nat.reduceMod,Nat.reduceDiv,ite_true]
    have heq : d+1-2+1=d := by omega
    rw [heq]
  rw [hev]
  simp only [Option.bind_some]
  rw [drainB]
  simp

theorem next_four_odd (d : Nat) (hd : d%2=1) (h7 : 7≤d) :
    highLevelNext (.D 4 d) = some (.D (d+1) 12) := by
  simp only [highLevelNext,if_neg (by decide : (4:Nat)≠0)]
  have h1 : ¬ (d%2=1 ∧ (4:Nat)≥d+5) := by omega
  have h2 : ¬ (d%2=0 ∧ (4:Nat)≥d+3) := by omega
  have h4 : 4 ≠ d+2 := by omega
  simp only [if_neg h1,if_neg h2,if_neg (by decide : (4:Nat)%2≠1),
    if_neg h4,if_pos hd]
  have hx : d+4-4=d := by omega
  rw [hx,drain_three_exact]

theorem next_four_even (d : Nat) (hd : d%2=0) (h7 : 7≤d) :
    highLevelNext (.D 4 d) = some (.D (d-6) 23) := by
  simp only [highLevelNext,if_neg (by decide : (4:Nat)≠0)]
  have h1 : ¬ (d%2=1 ∧ (4:Nat)≥d+5) := by omega
  have h2 : ¬ (d%2=0 ∧ (4:Nat)≥d+3) := by omega
  have h4 : 4 ≠ d+2 := by omega
  have hodd : d%2≠1 := by omega
  simp only [if_neg h1,if_neg h2,if_neg (by decide : (4:Nat)%2≠1),
    if_neg h4,if_neg hodd]
  have hx : d+1-4=d-3 := by omega
  rw [hx,evalA_four_first (d-3) 13 (by omega)]
  simp only [Option.bind_some]
  rw [drainB]
  congr 1 <;> omega

theorem next_six_odd (d : Nat) (hd : d%2=1) (h7 : 7≤d) :
    highLevelNext (.D 6 d) = some (.D (d-5) 26) := by
  simp only [highLevelNext,if_neg (by decide : (6:Nat)≠0)]
  have h1 : ¬ (d%2=1 ∧ (6:Nat)≥d+5) := by omega
  have h2 : ¬ (d%2=0 ∧ (6:Nat)≥d+3) := by omega
  have h4 : 6 ≠ d+2 := by omega
  simp only [if_neg h1,if_neg h2,if_neg (by decide : (6:Nat)%2≠1),
    if_neg h4,if_pos hd]
  have hx : d+4-6=d-2 := by omega
  rw [hx,drain_five_exact (d-2) 3 (by omega)]
  congr 1 <;> omega

theorem next_six_even (d : Nat) (hd : d%2=0) (h7 : 7≤d) :
    highLevelNext (.D 6 d) = some (.D (d-8) 31) := by
  simp only [highLevelNext,if_neg (by decide : (6:Nat)≠0)]
  have h1 : ¬ (d%2=1 ∧ (6:Nat)≥d+5) := by omega
  have h2 : ¬ (d%2=0 ∧ (6:Nat)≥d+3) := by omega
  have h4 : 6 ≠ d+2 := by omega
  have hodd : d%2≠1 := by omega
  simp only [if_neg h1,if_neg h2,if_neg (by decide : (6:Nat)%2≠1),
    if_neg h4,if_neg hodd]
  have hx : d+1-6=d-5 := by omega
  rw [hx]
  have he : evalA (d-5) 6 17 = some (d-6,2,19) := by
    rw [evalA]
    have hn : d-5≠0 := by omega
    simp only [if_neg (by decide : 6%3≠2),if_neg hn,
      if_pos (by decide : 6%3=0)]
    congr 1 <;> omega
  rw [he]
  simp only [Option.bind_some]
  rw [drain_two_exact (d-6) 19 (by omega)]
  congr 1 <;> omega

theorem next_eight_odd (d : Nat) (hd : d%2=1) (h7 : 7≤d) :
    highLevelNext (.D 8 d) = some (.D (d-7) 34) := by
  simp only [highLevelNext,if_neg (by decide : (8:Nat)≠0)]
  have h1 : ¬ (d%2=1 ∧ (8:Nat)≥d+5) := by omega
  have h2 : ¬ (d%2=0 ∧ (8:Nat)≥d+3) := by omega
  have h4 : 8 ≠ d+2 := by omega
  simp only [if_neg h1,if_neg h2,if_neg (by decide : (8:Nat)%2≠1),
    if_neg h4,if_pos hd]
  have hx : d+4-8=d-4 := by omega
  rw [hx,drain_seven_exact (d-4) 3 (by omega)]
  congr 1 <;> omega

theorem next_eight_even (d : Nat) (hd : d%2=0) (h7 : 7≤d) :
    highLevelNext (.D 8 d) = some (.D (d-8) 33) := by
  simp only [highLevelNext,if_neg (by decide : (8:Nat)≠0)]
  have h1 : ¬ (d%2=1 ∧ (8:Nat)≥d+5) := by omega
  have h2 : ¬ (d%2=0 ∧ (8:Nat)≥d+3) := by omega
  have h4 : 8 ≠ d+2 := by omega
  have hodd : d%2≠1 := by omega
  simp only [if_neg h1,if_neg h2,if_neg (by decide : (8:Nat)%2≠1),
    if_neg h4,if_neg hodd]
  have hx : d+1-8=d-7 := by omega
  rw [hx]
  have he : evalA (d-7) 8 21 = some (d-6,2,21) := by
    rw [evalA]
    simp only [Nat.reduceMod,Nat.reduceDiv,ite_true]
    have heq : d-7+1=d-6 := by omega
    rw [heq]
  rw [he]
  simp only [Option.bind_some]
  rw [drain_two_exact (d-6) 21 (by omega)]
  congr 1 <;> omega


/-- Exact low-third-coordinate IMAGE on the positive even-root-compatible strip.
Every other surviving output has third counter at least 23. -/
theorem next_low_third_spectrum (a d aa dd : Nat)
    (ha : a%2=0) (hd : 7≤d)
    (h : highLevelNext (.D a d)=some (.D aa dd)) :
    dd=7 ∨ dd=9 ∨ dd=10 ∨ dd=12 ∨ dd=14 ∨ 23≤dd := by
  by_cases hlarge : 10≤a
  · right;right;right;right;right
    have h29:= next_large_third_ge_29 a d aa dd ha hlarge hd h
    omega
  · have hsmall : a=0 ∨ a=2 ∨ a=4 ∨ a=6 ∨ a=8 := by omega
    rcases hsmall with rfl | rfl | rfl | rfl | rfl
    · by_cases hodd : d%2=1
      · rw [axis_odd_exact d hodd] at h
        cases h
        simp
      · have heven : d%2=0 := by omega
        simp [highLevelNext,heven] at h
        cases h
        omega
    · by_cases hodd : d%2=1
      · rw [next_two_odd d hodd hd] at h
        cases h
        simp
      · have heven : d%2=0 := by omega
        rw [next_two_even d heven hd] at h
        cases h
        simp
    · by_cases hodd : d%2=1
      · rw [next_four_odd d hodd hd] at h
        cases h
        simp
      · have heven : d%2=0 := by omega
        rw [next_four_even d heven hd] at h
        cases h
        omega
    · by_cases hodd : d%2=1
      · rw [next_six_odd d hodd hd] at h
        cases h
        omega
      · have heven : d%2=0 := by omega
        rw [next_six_even d heven hd] at h
        cases h
        omega
    · by_cases hodd : d%2=1
      · rw [next_eight_odd d hodd hd] at h
        cases h
        omega
      · have heven : d%2=0 := by omega
        rw [next_eight_even d heven hd] at h
        cases h
        omega

theorem run_third_ge_seven (n a d : Nat)
    (h : run n = some (.D a d)) : 7≤d := by
  induction n generalizing a d with
  | zero =>
    simp only [run] at h
    cases h
    omega
  | succ n ih =>
    simp only [run] at h
    cases hr : run n with
    | none => simp [hr] at h
    | some s =>
      rcases s with ⟨a0,d0⟩
      simp only [hr,Option.bind_some] at h
      have hprev := ih a0 d0 hr
      have heven := run_preserves_even n a0 d0 hr
      exact next_even_third_ge_seven a0 d0 a d heven hprev h

/-- A global blank-origin exclusion, conditional only on the section visit existing. -/
theorem run_third_not_eight (n a : Nat) :
    run n ≠ some (.D a 8) := by
  intro h
  have hseven := run_third_ge_seven n a 8 h
  cases n with
  | zero => simp [run] at h
  | succ n =>
    simp only [run] at h
    cases hr : run n with
    | none => simp [hr] at h
    | some s =>
      rcases s with ⟨a0,d0⟩
      simp only [hr,Option.bind_some] at h
      exact next_forbids_eight a0 d0 a
        (run_preserves_even n a0 d0 hr)
        (run_third_ge_seven n a0 d0 hr) h

theorem run_low_third_spectrum (n a d : Nat)
    (h : run n=some (.D a d)) :
    d=7 ∨ d=9 ∨ d=10 ∨ d=12 ∨ d=14 ∨ 23≤d := by
  cases n with
  | zero =>
    simp only [run] at h
    cases h
    simp
  | succ n =>
    simp only [run] at h
    cases hr : run n with
    | none => simp [hr] at h
    | some s =>
      rcases s with ⟨a0,d0⟩
      simp only [hr,Option.bind_some] at h
      exact next_low_third_spectrum a0 d0 a d
        (run_preserves_even n a0 d0 hr)
        (run_third_ge_seven n a0 d0 hr) h

#print axioms next_low_third_spectrum
#print axioms run_low_third_spectrum
#print axioms run_third_ge_seven
#print axioms run_third_not_eight
#print axioms evalA_third_ge
#print axioms next_even_third_ge_seven
#print axioms next_forbids_eight

end BB6.Agent8RootSpectrumSource
