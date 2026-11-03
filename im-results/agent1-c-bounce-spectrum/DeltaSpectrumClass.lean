import DeltaSpectrum
import PositiveMassOriginal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Elementary exhaustive classification of all integers at least four
    outside the congruence class two modulo six. -/
private theorem nat_gain_classification (d : Nat)
    (hge : 4 ≤ d) (hmod : d%6 ≠ 2) :
    d=4 ∨ d=6 ∨ (∃n, d=5+6*n) ∨
    (∃n, d=7+3*n) ∨ (∃n, d=9+3*n) := by
  have hm : d%6=0 ∨ d%6=1 ∨ d%6=3 ∨ d%6=4 ∨ d%6=5 := by omega
  rcases hm with h0 | h1 | h3 | h4 | h5
  · by_cases hb : d/6=1
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨2*(d/6)-3,by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨2*(d/6-1),by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨2*(d/6-1),by omega⟩)))
  · by_cases hd4 : d=4
    · exact Or.inl hd4
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨2*(d/6)-1,by omega⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨d/6,by omega⟩))

/-- The actual positive-right section gain has no residue two modulo six.
    In particular, the smallest impossible candidate is mass delta eight. -/
theorem section_gain_mod6_ne_two (a k x y : Nat)
    (hk : 0<k) (h : secNext (a,k)=some (x,y)) :
    ((x+2*y)-(a+2*k))%6 ≠ 2 := by
  have hmass := section_mass_four_if_right_positive a k x y hk h
  intro he
  let d := (x+2*y)-(a+2*k)
  have hd : 4≤d := by dsimp [d]; omega
  have hmod : d%6=2 := he
  have hq : 1≤d/6 := by omega
  have hbad : x+2*y = a+2*k+8+6*(d/6-1) := by
    dsimp [d] at hmod hq
    omega
  exact section_no_gain_8_plus_6r a k x y (d/6-1) hk h hbad

/-- Exhaustive permitted arithmetic superclasses for positive-right gains.
    This is only a NECESSARY condition: no claim every listed gain occurs. -/
theorem section_gain_possible_classes (a k x y : Nat)
    (hk : 0<k) (h : secNext (a,k)=some (x,y)) :
    ∃d : Nat, x+2*y=a+2*k+d ∧
      (d=4 ∨ d=6 ∨ (∃n, d=5+6*n) ∨
        (∃n, d=7+3*n) ∨ (∃n, d=9+3*n)) := by
  let d := (x+2*y)-(a+2*k)
  have hmass := section_mass_four_if_right_positive a k x y hk h
  have hd : 4≤d := by dsimp [d]; omega
  have hmod : d%6≠2 := section_gain_mod6_ne_two a k x y hk h
  exact ⟨d, by dsimp [d]; omega, nat_gain_classification d hd hmod⟩

#print axioms section_gain_mod6_ne_two
#print axioms section_gain_possible_classes
end BB6.Agent46
