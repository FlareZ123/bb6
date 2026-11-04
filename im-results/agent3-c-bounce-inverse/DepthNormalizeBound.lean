import OddForcedDepth
import Lean.Elab.Tactic.Omega
namespace BB6.Agent3

def depthNext (s : Nat × Nat) : Option (Nat × Nat) :=
  if oddLowGate s.1 s.2 then some (depthParentOdd s.1 s.2)
  else if evenSevenGate s.1 s.2 then some (depthParentSeven s.1 s.2)
  else none

def depthFuel : Nat → Nat × Nat → Nat × Nat
  | 0, s => s
  | n+1, s =>
      match depthNext s with
      | some t => depthFuel n t
      | none => s

private theorem depthNext_edge (s t : Nat × Nat)
    (h : depthNext s = some t) : depthForcedEdge s t := by
  by_cases ho : oddLowGate s.1 s.2
  · have eq : t=depthParentOdd s.1 s.2 := by
      simpa [depthNext,ho] using h.symm
    exact Or.inl ⟨ho,eq⟩
  · by_cases hs : evenSevenGate s.1 s.2
    · have eq : t=depthParentSeven s.1 s.2 := by
        simpa [depthNext,ho,hs] using h.symm
      exact Or.inr ⟨hs,eq⟩
    · simp [depthNext,ho,hs] at h

private theorem depthNext_terminal (s : Nat × Nat)
    (h : depthNext s = none) :
    oddForcedNormalize s.1 s.2=s := by
  have ho : ¬oddLowGate s.1 s.2 := by
    intro hh
    simp [depthNext,hh] at h
  have hs : ¬evenSevenGate s.1 s.2 := by
    intro hh
    simp [depthNext,ho,hh] at h
  rw [oddForcedNormalize]
  simp [ho,hs]

private theorem depthNext_norm (s t : Nat × Nat)
    (h : depthNext s = some t) :
    oddForcedNormalize s.1 s.2 = oddForcedNormalize t.1 t.2 := by
  by_cases ho : oddLowGate s.1 s.2
  · have eq : t=depthParentOdd s.1 s.2 := by
      simpa [depthNext,ho] using h.symm
    subst t
    rw [oddForcedNormalize]
    simp [ho,depthParentOdd]
  · by_cases hs : evenSevenGate s.1 s.2
    · have eq : t=depthParentSeven s.1 s.2 := by
        simpa [depthNext,ho,hs] using h.symm
      subst t
      rw [oddForcedNormalize]
      simp [ho,hs,depthParentSeven]
    · simp [depthNext,ho,hs] at h

private theorem depth_three_terminal (s : Nat × Nat) :
    depthNext (depthFuel 3 s) = none := by
  simp only [depthFuel]
  cases h1 : depthNext s with
  | none => simpa [depthFuel,h1] using h1
  | some t =>
    cases h2 : depthNext t with
    | none => simpa [depthFuel,h1,h2] using h2
    | some u =>
      cases h3 : depthNext u with
      | none => simpa [depthFuel,h1,h2,h3] using h3
      | some v =>
        by_cases h4 : depthNext v = none
        · simpa [depthFuel,h1,h2,h3] using h4
        · cases h5 : depthNext v with
          | none => contradiction
          | some w =>
            have hbad := depth_no_four s t u v w
              (depthNext_edge s t h1)
              (depthNext_edge t u h2)
              (depthNext_edge u v h3)
              (depthNext_edge v w h5)
            exact False.elim hbad

private theorem depthFuel_eq_norm_of_terminal (n : Nat) (s : Nat × Nat)
    (h : depthNext (depthFuel n s)=none) :
    oddForcedNormalize s.1 s.2=depthFuel n s := by
  induction n generalizing s with
  | zero =>
      simpa [depthFuel] using depthNext_terminal s (by simpa [depthFuel] using h)
  | succ n ih =>
      cases hs : depthNext s with
      | none =>
          simpa [depthFuel,hs] using depthNext_terminal s hs
      | some t =>
          have hrec : depthNext (depthFuel n t)=none := by
            simpa [depthFuel,hs] using h
          calc
            oddForcedNormalize s.1 s.2 = oddForcedNormalize t.1 t.2 := depthNext_norm s t hs
            _ = depthFuel n t := ih t hrec
            _ = depthFuel (n+1) s := by simp [depthFuel,hs]

/-- Every input to the unbounded original recursion has exactly the same normal
    form as three fixed arithmetic inverse operations. -/
theorem oddForcedNormalize_eq_three (x y : Nat) :
    oddForcedNormalize x y = depthFuel 3 (x,y) :=
  depthFuel_eq_norm_of_terminal 3 (x,y) (depth_three_terminal (x,y))
#print axioms oddForcedNormalize_eq_three
end BB6.Agent3
