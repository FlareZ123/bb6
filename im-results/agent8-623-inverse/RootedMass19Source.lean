import Agent8RootedMassSource
import Agent8SharpMass12Source

/-!
Source-connected nineteen-unit two-return mass advance for BB6 cryptid #623.
Imports the unmodified pinned Cryptids accelerator through the predecessor
original-source proof modules. No halting decision follows.
-/
namespace BB6.Agent8SharpSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
private abbrev next : HighLevelState → Option HighLevelState := highLevelNext

theorem small_even_escape_positive (a d aa dd : Nat)
    (ha : a%2=0) (hsmall : a≤4) (hmass : 16≤a+d)
    (hstep : next (.D a d) = some (.D aa dd)) : 6≤aa ∧ 0<dd := by
  have hcases : a=0 ∨ a=2 ∨ a=4 := by omega
  rcases hcases with h0 | h2 | h4
  · subst a
    simp only [next,highLevelNext, if_pos rfl] at hstep
    by_cases hd : d%2=1
    · simp only [if_pos hd] at hstep
      rw [drain_two_exact (d+1) (by omega)] at hstep
      cases hstep
      omega
    · simp only [if_neg hd] at hstep
      cases hstep
      omega
  · subst a
    simp only [next,highLevelNext, if_neg (by decide : (2:Nat)≠0)] at hstep
    have hs1 : ¬ (d%2=1 ∧ (2:Nat)≥d+5) := by omega
    have hs2 : ¬ (d%2=0 ∧ (2:Nat)≥d+3) := by omega
    simp only [if_neg hs1, if_neg hs2, if_neg (by decide : (2:Nat)%2≠1)] at hstep
    by_cases hd : d%2=1
    · have heq : 2 ≠ d+2 := by omega
      simp only [if_neg heq, if_pos hd] at hstep
      have harg : d+4-2=d+2 := by omega
      simp only [harg,Nat.reduceSub] at hstep
      rw [drain_one_exact (d+2) (by omega)] at hstep
      cases hstep
      omega
    · have heq : 2 ≠ d+2 := by omega
      simp only [if_neg heq, if_neg hd] at hstep
      have he : evalA (d+1-2) 2 (2*2+5) = some (d,0,9) := by
        rw [evalA]
        simp only [if_pos (by decide : 2%3=2)]
        simp only [if_true, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd,Option.some.injEq,Prod.mk.injEq,true_and,and_true]
        omega
      rw [he] at hstep
      simp only [Option.bind_some] at hstep
      rw [drainB] at hstep
      simp only [if_pos (by decide : (0:Nat)=0)] at hstep
      cases hstep
      omega
  · subst a
    simp only [next,highLevelNext, if_neg (by decide : (4:Nat)≠0)] at hstep
    have hs1 : ¬ (d%2=1 ∧ (4:Nat)≥d+5) := by omega
    have hs2 : ¬ (d%2=0 ∧ (4:Nat)≥d+3) := by omega
    have heq : 4 ≠ d+2 := by omega
    simp only [if_neg hs1, if_neg hs2, if_neg (by decide : (4:Nat)%2≠1), if_neg heq] at hstep
    by_cases hd : d%2=1
    · simp only [if_pos hd] at hstep
      have heq2 : d+4-4=d := by omega
      rw [heq2,drain_three_exact] at hstep
      cases hstep
      omega
    · simp only [if_neg hd] at hstep
      have heq2 : d+1-4=d-3 := by omega
      rw [heq2, eval_four_exact (d-3) 13 (by omega)] at hstep
      simp only [Option.bind_some] at hstep
      rw [drainB] at hstep
      simp only [if_pos (by decide : (0:Nat)=0)] at hstep
      cases hstep
      omega

/-- The zero-second-counter ray immediately escapes to positive second counter. -/
theorem high_zero_exact (a : Nat) (ha : 16≤a) :
    next (.D a 0) = some (.D (a-4) 14) := by
  simp only [next,highLevelNext]
  have h0 : a ≠ 0 := by omega
  simp only [if_neg h0]
  have h1 : ¬ ((0:Nat)%2=1 ∧ a≥(0:Nat)+5) := by omega
  simp only [if_neg h1]
  have harg : a-0-2=a-2 := by omega
  rw [harg, drain_two_exact (a-2) (by omega)]
  have h3 : a ≥ (0:Nat)+3 := by omega
  simp only [true_and, if_pos h3]
  congr 1 <;> omega

/-- For high-mass even-a pairs, a successful two-return trajectory gains 19. -/
theorem two_step_gain_19 (a d b e c f : Nat)
    (ha : a%2=0) (hb : b%2=0) (hmass : 16≤a+d)
    (h1 : next (.D a d) = some (.D b e))
    (h2 : next (.D b e) = some (.D c f))
    (h7first : a+d+7≤b+e) (h7second : b+e+7≤c+f) :
    a+d+19≤c+f := by
  by_cases hhigh : 6≤a
  · by_cases hdpos : 0<d
    · have hm := next_even_six_positive_d_mass a d b e ha hhigh hdpos h1
      omega
    · have hd0 : d=0 := by omega
      subst d
      have hzeros := high_zero_exact a (by omega)
      rw [hzeros] at h1
      cases h1
      have h12 := next_even_six_positive_d_mass (a-4) 14 c f
        (by omega) (by omega) (by omega) h2
      omega
  · have hsmall : a≤4 := by omega
    have hesc := small_even_escape_positive a d b e ha hsmall hmass h1
    have h12 := next_even_six_positive_d_mass b e c f hb hesc.1 hesc.2 h2
    omega

/-- Genuine D(0,7) orbit, all surviving pairs beginning at n≥2. -/
theorem root_two_step_gain_19 (n a d c f : Nat)
    (hn : 2 ≤ n)
    (hbefore : run n = some (.D a d))
    (hafter : run (n+2) = some (.D c f)) :
    a+d+19 ≤ c+f := by
  have hbig : 16 ≤ a+d := by
    have h := run_grows_at_least_seven n a d hbefore
    omega
  have heven := run_preserves_even n a d hbefore
  cases hmid : next (.D a d) with
  | none =>
    have hm : run (n+1) = none := by
      change (run n).bind highLevelNext = none
      rw [hbefore]
      exact hmid
    have hz : run (n+2) = none := by
      change (run (n+1)).bind highLevelNext = none
      rw [hm]
      rfl
    simp [hz] at hafter
  | some s =>
    rcases s with ⟨b,e⟩
    have hmidrun : run (n+1) = some (.D b e) := by
      change (run n).bind highLevelNext = some (.D b e)
      rw [hbefore]
      exact hmid
    have hstep2 : next (.D b e) = some (.D c f) := by
      change (run (n+1)).bind highLevelNext = some (.D c f) at hafter
      rw [hmidrun] at hafter
      exact hafter
    have heven2 := run_preserves_even (n+1) b e hmidrun
    have h7a := next_strict_mass a d b e hmid
    have h7b := next_strict_mass b e c f hstep2
    exact two_step_gain_19 a d b e c f heven heven2 hbig hmid hstep2 h7a h7b

/-- At surviving even-index returns n=2k+2, mass is at least 37+19k. -/
theorem root_even_mass_bound_19 (k a d : Nat)
    (h : run (2*k+2) = some (.D a d)) :
    37 + 19*k ≤ a+d := by
  induction k generalizing a d with
  | zero =>
    have h2 : run 2 = some (.D 6 31) := by decide +kernel
    have hh : run 2 = some (.D a d) := by simpa using h
    rw [h2] at hh
    cases hh
    omega
  | succ k ih =>
    let n : Nat := 2*k+2
    have htarget : run (n+2) = some (.D a d) := by
      have hre : n+2 = 2*(k+1)+2 := by dsimp [n]; omega
      rw [hre]
      exact h
    cases hp : run n with
    | none =>
      have hp1 : run (n+1) = none := by
        change (run n).bind highLevelNext = none
        rw [hp]
        rfl
      have hz : run (n+2) = none := by
        change (run (n+1)).bind highLevelNext = none
        rw [hp1]
        rfl
      rw [hz] at htarget
      contradiction
    | some st =>
      rcases st with ⟨ap,dp⟩
      have hprev : run (2*k+2) = some (.D ap dp) := by simpa only [n] using hp
      have hbound : 37+19*k ≤ ap+dp := ih ap dp hprev
      have hstep := root_two_step_gain_19 n ap dp a d (by dsimp [n]; omega) hp htarget
      omega

/-- At surviving odd-index returns n=2k+3, mass is at least 44+19k. -/
theorem root_odd_mass_bound_19 (k a d : Nat)
    (h : run (2*k+3) = some (.D a d)) :
    44 + 19*k ≤ a+d := by
  cases hp : run (2*k+2) with
  | none =>
    have hz : run (2*k+3) = none := by
      change (run (2*k+2)).bind highLevelNext = none
      rw [hp]
      rfl
    rw [hz] at h
    contradiction
  | some st =>
    rcases st with ⟨ap,dp⟩
    have hbound := root_even_mass_bound_19 k ap dp hp
    have hnext : next (.D ap dp) = some (.D a d) := by
      change (run (2*k+2)).bind highLevelNext = some (.D a d) at h
      rw [hp] at h
      exact h
    have h7 := next_strict_mass ap dp a d hnext
    omega

#print axioms small_even_escape_positive
#print axioms two_step_gain_19
#print axioms root_two_step_gain_19
#print axioms root_even_mass_bound_19
#print axioms root_odd_mass_bound_19
end BB6.Agent8SharpSource
