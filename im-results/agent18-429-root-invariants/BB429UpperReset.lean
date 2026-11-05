import BB429OddResetGate
import Lean.Elab.Tactic.Omega
namespace BB429UpperReset
set_option maxHeartbeats 20000000
set_option maxRecDepth 30000

/-- Every genuine blank-root upper reset predecessor with counter 12 mod16
    would have a 7 mod8 ancestor with forbidden second counter 5 mod8. -/
theorem no_upper_twelve (n u : Nat)
    (hr : BB429.run n (0,0)=some (u,2*u+2))
    (hu : u%16=12) : False := by
  cases n with
  | zero => simp [BB429.run] at hr
  | succ n =>
      simp only [BB429.run] at hr
      cases hp : BB429.run n (0,0) with
      | none => simp [hp] at hr
      | some p =>
          simp only [hp,Option.bind_some] at hr
          obtain ⟨h1,h2,h3⟩ :=
            BB429OddResetGate.incoming_even p.1 p.2 u (2*u+2) hr (by omega) (by omega)
          have h7 := BB429SevenStrong.rooted_seven_strong n p.1 p.2 hp (by omega)
          omega

/-- A sufficiently large odd output with second counter 0 mod4
    must come from the first, doubling transition. -/
theorem odd_zero_mod4_first (x y a b : Nat)
    (hs : BB429.next (x,y)=some (a,b))
    (ha : 9≤a) (ho : a%2=1) (hb : b%4=0) :
    a=2*x+3 ∧ y=b+a := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

/-- The blank orbit never visits zero-first counter, second counter 32.
    This is an exact bounded consequence of rank growth >=3. -/
theorem no_zero_thirty_two (n : Nat) :
    BB429.run n (0,0) ≠ some (0,32) := by
  intro hr
  have hb := (BB429.run_rank_bounds (0,0) (0,32) n hr).1
  have hn : n≤10 := by simp [BB429.rank] at hb; omega
  have he : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨
      n=6 ∨ n=7 ∨ n=8 ∨ n=9 ∨ n=10 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [BB429.run, BB429.next] at hr

/-- Exact all-parameter exclusion of the upper source boundary
    with first counter 9(mod16), including the finite q=0 case. -/
theorem no_upper_nine (n u : Nat)
    (hr : BB429.run n (0,0)=some (u,2*u+2))
    (hu : u%16=9) : False := by
  let q := u/16
  have hu0 : u=16*q+9 := by dsimp [q]; omega
  have hb0 : 2*u+2=32*q+20 := by omega
  cases n with
  | zero => simp [BB429.run] at hr
  | succ n =>
      simp only [BB429.run] at hr
      cases hp : BB429.run n (0,0) with
      | none => simp [hp] at hr
      | some p =>
          simp only [hp,Option.bind_some] at hr
          obtain ⟨h1,h2⟩ := odd_zero_mod4_first p.1 p.2 u (2*u+2) hr (by omega) (by omega) (by omega)
          have hx : p.1=8*q+3 := by omega
          have hy : p.2=48*q+29 := by omega
          have hh : BB429.run n (0,0)=some (8*q+3,48*q+29) := by
            have heq : p=(8*q+3,48*q+29) := Prod.ext hx hy
            rw [heq] at hp
            exact hp
          cases n with
          | zero =>
              simp [BB429.run] at hh
          | succ n =>
              simp only [BB429.run] at hh
              cases hp2 : BB429.run n (0,0) with
              | none => simp [hp2] at hh
              | some v =>
                  simp only [hp2,Option.bind_some] at hh
                  obtain ⟨hxx,hyy⟩ :=
                    BB429OddResetGate.incoming_odd_second v.1 v.2
                      (8*q+3) (48*q+29) hh (by omega)
                  have hvx : v.1=4*q := by omega
                  have hvy : v.2=56*q+32 := by omega
                  by_cases hq : q=0
                  · have hz : BB429.run n (0,0)=some (0,32) := by
                      have hveq : v=(0,32) := Prod.ext (by omega) (by omega)
                      rw [hveq] at hp2
                      exact hp2
                    exact no_zero_thirty_two n hz
                  · have ha : 0<v.1 := by omega
                    have he : v.1%2=0 := by omega
                    have hs := BB429RootEven8.rooted_positive_even_eight n v.1 v.2 hp2 ha he
                    omega

/-- Five necessary congruence classes remain for genuine upper-boundary reset.
    This need not imply a reset will occur in any of them. -/
theorem upper_necessary_five (n u : Nat)
    (hr : BB429.run n (0,0)=some (u,2*u+2)) :
    u%16=0 ∨ u%16=4 ∨ u%16=5 ∨ u%16=8 ∨ u%16=13 := by
  have hh := BB429OddResetGate.rooted_top_two_predecessor n u hr
  have h12 : u%16≠12 := by intro h; exact no_upper_twelve n u hr h
  have h9 : u%16≠9 := by intro h; exact no_upper_nine n u hr h
  omega

#print axioms no_upper_twelve
#print axioms odd_zero_mod4_first
#print axioms no_zero_thirty_two
#print axioms no_upper_nine
#print axioms upper_necessary_five
end BB429UpperReset
