import SourceBound
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Depth
open BB6.Agent3

/-- The exact one-step dispatcher of the original, unbounded
    FullForcedNormalize, stopping when all three source guards fail. -/
def forcedNext (s : Nat × Nat) : Option (Nat × Nat) :=
  if oddLowGate s.1 s.2 then
    some ((s.1+s.2-4)/2,(s.1+3*s.2-10)/4)
  else if evenSevenGate s.1 s.2 then
    some ((s.1+s.2-5)/2,(s.1+3*s.2-9)/4)
  else if evenAffineGate s.1 s.2 then
    some (s.1+s.2-2,(s.2-2)/2)
  else none

/-- Iterate only the exact original-source guards, with bounded fuel. -/
def forcedFuel : Nat → Nat × Nat → Nat × Nat
  | 0, s => s
  | n+1, s =>
    match forcedNext s with
    | some t => forcedFuel n t
    | none => s

private theorem forcedNext_edge (s t : Nat × Nat)
    (h : forcedNext s = some t) :
    forcedEdge s.1 s.2 t.1 t.2 := by
  by_cases ho : oddLowGate s.1 s.2
  · have ht : t = ((s.1+s.2-4)/2,(s.1+3*s.2-10)/4) := by
      simpa [forcedNext,ho] using h.symm
    exact Or.inl ⟨ho, by simpa [ht], by simpa [ht]⟩
  · by_cases he : evenSevenGate s.1 s.2
    · have ht : t = ((s.1+s.2-5)/2,(s.1+3*s.2-9)/4) := by
        simpa [forcedNext,ho,he] using h.symm
      exact Or.inr (Or.inl ⟨he, by simpa [ht], by simpa [ht]⟩)
    · by_cases ha : evenAffineGate s.1 s.2
      · have ht : t = (s.1+s.2-2,(s.2-2)/2) := by
          simpa [forcedNext,ho,he,ha] using h.symm
        exact Or.inr (Or.inr ⟨ha, by simpa [ht], by simpa [ht]⟩)
      · simp [forcedNext,ho,he,ha] at h

private theorem forcedNext_terminal (s : Nat × Nat)
    (h : forcedNext s = none) :
    fullForcedNormalize s.1 s.2 = s := by
  have ho : ¬oddLowGate s.1 s.2 := by
    intro hh
    simp [forcedNext,hh] at h
  have he : ¬evenSevenGate s.1 s.2 := by
    intro hh
    simp [forcedNext,ho,hh] at h
  have ha : ¬evenAffineGate s.1 s.2 := by
    intro hh
    simp [forcedNext,ho,he,hh] at h
  rw [fullForcedNormalize]
  simp [ho,he,ha]

private theorem forcedNext_norm (s t : Nat × Nat)
    (h : forcedNext s = some t) :
    fullForcedNormalize s.1 s.2 = fullForcedNormalize t.1 t.2 := by
  by_cases ho : oddLowGate s.1 s.2
  · have ht : t = ((s.1+s.2-4)/2,(s.1+3*s.2-10)/4) := by
      simpa [forcedNext,ho] using h.symm
    subst t
    rw [fullForcedNormalize]
    simp [ho]
  · by_cases he : evenSevenGate s.1 s.2
    · have ht : t = ((s.1+s.2-5)/2,(s.1+3*s.2-9)/4) := by
        simpa [forcedNext,ho,he] using h.symm
      subst t
      rw [fullForcedNormalize]
      simp [ho,he]
    · by_cases ha : evenAffineGate s.1 s.2
      · have ht : t = (s.1+s.2-2,(s.2-2)/2) := by
          simpa [forcedNext,ho,he,ha] using h.symm
        subst t
        rw [fullForcedNormalize]
        simp [ho,he,ha]
      · simp [forcedNext,ho,he,ha] at h

private theorem forcedFuel_eq_norm_of_terminal (n : Nat) (s : Nat × Nat)
    (h : forcedNext (forcedFuel n s) = none) :
    fullForcedNormalize s.1 s.2 = forcedFuel n s := by
  induction n generalizing s with
  | zero =>
      simpa [forcedFuel] using forcedNext_terminal s (by simpa [forcedFuel] using h)
  | succ n ih =>
      cases hs : forcedNext s with
      | none =>
          simpa [forcedFuel,hs] using forcedNext_terminal s hs
      | some t =>
          have hrec : forcedNext (forcedFuel n t) = none := by
            simpa [forcedFuel,hs] using h
          calc
            fullForcedNormalize s.1 s.2 =
                fullForcedNormalize t.1 t.2 := forcedNext_norm s t hs
            _ = forcedFuel n t := ih t hrec
            _ = forcedFuel (n+1) s := by simp [forcedFuel,hs]

private theorem terminal_four_mass_one (s : Nat × Nat)
    (hm : (s.1+2*s.2)%4=1) :
    forcedNext (forcedFuel 4 s) = none := by
  cases h1 : forcedNext s with
  | none => simpa [forcedFuel,h1] using h1
  | some t =>
    cases h2 : forcedNext t with
    | none => simpa [forcedFuel,h1,h2] using h2
    | some u =>
      cases h3 : forcedNext u with
      | none => simpa [forcedFuel,h1,h2,h3] using h3
      | some v =>
        cases h4 : forcedNext v with
        | none => simpa [forcedFuel,h1,h2,h3,h4] using h4
        | some w =>
          by_cases h5 : forcedNext w = none
          · simpa [forcedFuel,h1,h2,h3,h4] using h5
          · cases h5' : forcedNext w with
            | none => contradiction
            | some z =>
              have hbad := no_five_mass_one
                s.1 s.2 t.1 t.2 u.1 u.2 v.1 v.2 w.1 w.2 z.1 z.2 hm
                (forcedNext_edge s t h1)
                (forcedNext_edge t u h2)
                (forcedNext_edge u v h3)
                (forcedNext_edge v w h4)
                (forcedNext_edge w z h5')
              exact False.elim hbad

private theorem terminal_five_mass_zero (s : Nat × Nat)
    (hm : (s.1+2*s.2)%4=0) :
    forcedNext (forcedFuel 5 s) = none := by
  cases h1 : forcedNext s with
  | none => simpa [forcedFuel,h1] using h1
  | some t =>
    obtain ⟨he,hu,hv⟩ :=
      mass_zero_first_seven s.1 s.2 t.1 t.2 hm (forcedNext_edge s t h1)
    have hm1 := mass_zero_seven_to_one s.1 s.2 t.1 t.2 hm he hu hv
    have ht := terminal_four_mass_one t hm1
    simpa [forcedFuel,h1] using ht

/-- For every natural x,y in weighted-mass class one, the unbounded,
    genuine Machine C forced normalizer is exactly four finite iterations. -/
theorem full_normalizer_four_mass_one (x y : Nat)
    (hm : (x+2*y)%4=1) :
    fullForcedNormalize x y = forcedFuel 4 (x,y) :=
  forcedFuel_eq_norm_of_terminal 4 (x,y)
    (terminal_four_mass_one (x,y) hm)

/-- In weighted-mass class zero, five iterations exactly compute the
    genuine source-defined, unbounded normalizer. -/
theorem full_normalizer_five_mass_zero (x y : Nat)
    (hm : (x+2*y)%4=0) :
    fullForcedNormalize x y = forcedFuel 5 (x,y) :=
  forcedFuel_eq_norm_of_terminal 5 (x,y)
    (terminal_five_mass_zero (x,y) hm)

#print axioms full_normalizer_four_mass_one
#print axioms full_normalizer_five_mass_zero
end BB6.Agent29Depth
