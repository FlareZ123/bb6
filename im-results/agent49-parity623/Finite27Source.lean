import Agent49TwoStep27Source

/-!
The finite 25..99 counter-mass strip is checked by Lean kernel reduction
for the unchanged Cryptids #623 highLevelNext, and the unbounded sector is
proved symbolically in Agent49TwoStep27Source. Together these give a sharp
27-unit mass gain for *all* two surviving transitions with even first
counter and initial mass >=25, including the genuine blank orbit from n=2.
No machine nonhalting conclusion is asserted. Source SHA:
c86f15861709b76042998c5211c7b2f83991621b.
-/

namespace BB6.Agent49Finite27Source
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
private abbrev next : HighLevelState → Option HighLevelState := highLevelNext

/-- Total, executable property over finite coordinates. Halting steps make
the implication vacuous; only two successful steps impose the 27 bound. -/
private def correct27 (a d : Nat) : Bool :=
  if (a % 2 == 0) && decide (25 ≤ a + d) && decide (a + d < 100) then
    match next (.D a d) with
    | none => true
    | some (.D b e) =>
      match next (.D b e) with
      | none => true
      | some (.D c f) => decide (a + d + 27 ≤ c + f)
  else true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finite_all_true : ∀ a d : Fin 100,
    correct27 a.val d.val = true := by decide +kernel

/-- No finite simulations are trusted: finite-all is a kernel proof term. -/
theorem small_gain27 (a d b e c f : Nat)
    (he : a%2=0) (hm : 25≤a+d) (hu : a+d<100)
    (h1 : next (.D a d)=some (.D b e))
    (h2 : next (.D b e)=some (.D c f)) :
    a+d+27≤c+f := by
  have ha : a<100 := by omega
  have hd : d<100 := by omega
  have hh := finite_all_true ⟨a,ha⟩ ⟨d,hd⟩
  simp [correct27,he,hm,hu,h1,h2] at hh
  omega

/-- Sharp, fully quantified two-return mass lower bound from counter mass 25. -/
theorem two_step_gain27_mass25 (a d b e c f : Nat)
    (he : a%2=0) (hm : 25≤a+d)
    (h1 : next (.D a d)=some (.D b e))
    (h2 : next (.D b e)=some (.D c f)) :
    a+d+27≤c+f := by
  by_cases hbig : 100≤a+d
  · exact BB6.Agent49TwoStep27Source.two_step_gain27_mass100
      a d b e c f he hbig h1 h2
  · exact small_gain27 a d b e c f he hm (by omega) h1 h2

/-- The constant 27 is optimal: synthetic D(0,26) returns through
D(26,7) and then D(14,39), realizing gain exactly 27. -/
theorem gain27_sharp_example :
    next (.D 0 26)=some (.D 26 7) ∧
    next (.D 26 7)=some (.D 14 39) := by
  constructor <;> decide +kernel

/-- For all surviving genuine blank-origin section returns at n>=2,
every subsequent surviving pair gains at least 27 mass units. -/
theorem root_two_step_gain27_from2 (n a d c f : Nat)
    (hn : 2≤n) (hbefore : run n=some (.D a d))
    (hafter : run (n+2)=some (.D c f)) :
    a+d+27≤c+f := by
  have hm : 25≤a+d := by
    by_cases heq : n=2
    · subst n
      have h2 : run 2=some (.D 6 31) := by decide +kernel
      rw [h2] at hbefore
      cases hbefore
      omega
    · have hbound := BB6.Agent49ParitySource.run_grows_at_least_seven n a d hbefore
      omega
  have ha := BB6.Agent49ParitySource.run_preserves_even n a d hbefore
  cases hmid : next (.D a d) with
  | none =>
    have hnone : run (n+1)=none := by
      change (run n).bind highLevelNext = none
      rw [hbefore]
      exact hmid
    have hnone2 : run (n+2)=none := by
      change (run (n+1)).bind highLevelNext = none
      rw [hnone]
      rfl
    rw [hnone2] at hafter
    contradiction
  | some st =>
    rcases st with ⟨b,e⟩
    have hmidrun : run (n+1)=some (.D b e) := by
      change (run n).bind highLevelNext = some (.D b e)
      rw [hbefore]
      exact hmid
    have hstep2 : next (.D b e)=some (.D c f) := by
      change (run (n+1)).bind highLevelNext = some (.D c f) at hafter
      rw [hmidrun] at hafter
      exact hafter
    exact two_step_gain27_mass25 a d b e c f ha hm hmid hstep2

/-- For each k>=0, a surviving genuine return at section 2k+2 has
total counter mass at least 37+27k. -/
theorem root_even_mass_bound27 (k a d : Nat)
    (h : run (2*k+2)=some (.D a d)) :
    37+27*k≤a+d := by
  induction k generalizing a d with
  | zero =>
    have h2 : run 2=some (.D 6 31) := by decide +kernel
    have hh : run 2=some (.D a d) := by simpa using h
    rw [h2] at hh
    cases hh
    omega
  | succ k ih =>
    let n : Nat := 2*k+2
    have htarget : run (n+2)=some (.D a d) := by
      have heq : n+2=2*(k+1)+2 := by dsimp [n]; omega
      rw [heq]
      exact h
    cases hp : run n with
    | none =>
      have hnone : run (n+1)=none := by
        change (run n).bind highLevelNext = none
        rw [hp]
        rfl
      have hnone2 : run (n+2)=none := by
        change (run (n+1)).bind highLevelNext = none
        rw [hnone]
        rfl
      rw [hnone2] at htarget
      contradiction
    | some st =>
      rcases st with ⟨ap,dp⟩
      have hprev : run (2*k+2)=some (.D ap dp) := by simpa only [n] using hp
      have hbound := ih ap dp hprev
      have hgain := root_two_step_gain27_from2 n ap dp a d
        (by dsimp [n]; omega) hp htarget
      omega

/-- An odd-index analogue anchored at the exact third section D(26,26). -/
theorem root_odd_mass_bound27 (k a d : Nat)
    (h : run (2*k+3)=some (.D a d)) :
    52+27*k≤a+d := by
  induction k generalizing a d with
  | zero =>
    have h3 : run 3=some (.D 26 26) := by decide +kernel
    have hh : run 3=some (.D a d) := by simpa using h
    rw [h3] at hh
    cases hh
    omega
  | succ k ih =>
    let n : Nat := 2*k+3
    have htarget : run (n+2)=some (.D a d) := by
      have heq : n+2=2*(k+1)+3 := by dsimp [n]; omega
      rw [heq]
      exact h
    cases hp : run n with
    | none =>
      have hnone : run (n+1)=none := by
        change (run n).bind highLevelNext = none
        rw [hp]
        rfl
      have hnone2 : run (n+2)=none := by
        change (run (n+1)).bind highLevelNext = none
        rw [hnone]
        rfl
      rw [hnone2] at htarget
      contradiction
    | some st =>
      rcases st with ⟨ap,dp⟩
      have hprev : run (2*k+3)=some (.D ap dp) := by simpa only [n] using hp
      have hbound := ih ap dp hprev
      have hgain := root_two_step_gain27_from2 n ap dp a d
        (by dsimp [n]; omega) hp htarget
      omega

#print axioms finite_all_true
#print axioms small_gain27
#print axioms two_step_gain27_mass25
#print axioms gain27_sharp_example
#print axioms root_two_step_gain27_from2
#print axioms root_even_mass_bound27
#print axioms root_odd_mass_bound27
/-- Exact genuinely blank-root sharpness witness, at section returns
four and six: mass 85 rises to 112, exactly 27 in two steps. -/
theorem blank_gain27_sharp :
    run 4=some (.D 2 83) ∧ run 6=some (.D 74 38) := by
  constructor <;> decide +kernel

/-- A refined rooted two-step bound anchored on the exact D(2,83) state.
This bound is attained by the genuine return at n=6. -/
theorem root_even_mass27_from4 (k a d : Nat)
    (h : run (4+2*k)=some (.D a d)) :
    85+27*k≤a+d := by
  induction k generalizing a d with
  | zero =>
    have h4 := blank_gain27_sharp.1
    have hh : run 4=some (.D a d) := by simpa using h
    rw [h4] at hh
    cases hh
    omega
  | succ k ih =>
    let n : Nat := 4+2*k
    have htarget : run (n+2)=some (.D a d) := by
      have heq : n+2=4+2*(k+1) := by dsimp [n]; omega
      rw [heq]
      exact h
    cases hp : run n with
    | none =>
      have hnone : run (n+1)=none := by
        change (run n).bind highLevelNext = none
        rw [hp]
        rfl
      have hnone2 : run (n+2)=none := by
        change (run (n+1)).bind highLevelNext = none
        rw [hnone]
        rfl
      rw [hnone2] at htarget
      contradiction
    | some st =>
      rcases st with ⟨ap,dp⟩
      have hprev : run (4+2*k)=some (.D ap dp) := by simpa only [n] using hp
      have hbound := ih ap dp hprev
      have hgain := root_two_step_gain27_from2 n ap dp a d
        (by dsimp [n]; omega) hp htarget
      omega

/-- A refined odd-index rooted mass lower bound from the exact fifth
return D(84,10), mass 94. -/
theorem root_odd_mass27_from5 (k a d : Nat)
    (h : run (5+2*k)=some (.D a d)) :
    94+27*k≤a+d := by
  induction k generalizing a d with
  | zero =>
    have h5 : run 5=some (.D 84 10) := by decide +kernel
    have hh : run 5=some (.D a d) := by simpa using h
    rw [h5] at hh
    cases hh
    omega
  | succ k ih =>
    let n : Nat := 5+2*k
    have htarget : run (n+2)=some (.D a d) := by
      have heq : n+2=5+2*(k+1) := by dsimp [n]; omega
      rw [heq]
      exact h
    cases hp : run n with
    | none =>
      have hnone : run (n+1)=none := by
        change (run n).bind highLevelNext = none
        rw [hp]
        rfl
      have hnone2 : run (n+2)=none := by
        change (run (n+1)).bind highLevelNext = none
        rw [hnone]
        rfl
      rw [hnone2] at htarget
      contradiction
    | some st =>
      rcases st with ⟨ap,dp⟩
      have hprev : run (5+2*k)=some (.D ap dp) := by simpa only [n] using hp
      have hbound := ih ap dp hprev
      have hgain := root_two_step_gain27_from2 n ap dp a d
        (by dsimp [n]; omega) hp htarget
      omega

#print axioms blank_gain27_sharp
#print axioms root_even_mass27_from4
#print axioms root_odd_mass27_from5

end BB6.Agent49Finite27Source
