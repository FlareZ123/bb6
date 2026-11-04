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

/-- Two fixed original-source reductions suffice for every input
    of weighted mass 2 modulo 4. -/
private theorem terminal_two_mass_two (s : Nat × Nat)
    (hm : (s.1+2*s.2)%4=2) :
    forcedNext (forcedFuel 2 s) = none := by
  cases h1 : forcedNext s with
  | none => simpa [forcedFuel,h1] using h1
  | some t =>
    cases h2 : forcedNext t with
    | none => simpa [forcedFuel,h1,h2] using h2
    | some u =>
      by_cases h3 : forcedNext u = none
      · simpa [forcedFuel,h1,h2] using h3
      · cases h3' : forcedNext u with
        | none => contradiction
        | some v =>
          exact False.elim (no_three_mass_two s.1 s.2 t.1 t.2
            u.1 u.2 v.1 v.2 hm
            (forcedNext_edge s t h1)
            (forcedNext_edge t u h2)
            (forcedNext_edge u v h3'))

theorem full_normalizer_two_mass_two (x y : Nat)
    (hm : (x+2*y)%4=2) :
    fullForcedNormalize x y = forcedFuel 2 (x,y) :=
  forcedFuel_eq_norm_of_terminal 2 (x,y)
    (terminal_two_mass_two (x,y) hm)

/-- For every one-left section state with odd second counter, a
    single source-forced predecessor is the entire forced normalizer. -/
private theorem terminal_one_left_odd (y : Nat) (hy : y%2=1) :
    forcedNext (forcedFuel 1 (1,y)) = none := by
  cases h1 : forcedNext (1,y) with
  | none => simpa [forcedFuel,h1] using h1
  | some t =>
    by_cases h2 : forcedNext t = none
    · simpa [forcedFuel,h1] using h2
    · cases h2' : forcedNext t with
      | none => contradiction
      | some u =>
        exact False.elim (one_left_odd_no_two y t.1 t.2 u.1 u.2 hy
          (forcedNext_edge (1,y) t h1)
          (forcedNext_edge t u h2'))

theorem full_normalizer_one_left_odd_one (y : Nat) (hy : y%2=1) :
    fullForcedNormalize 1 y = forcedFuel 1 (1,y) :=
  forcedFuel_eq_norm_of_terminal 1 (1,y)
    (terminal_one_left_odd y hy)

/-- Every one-left section input, regardless of its right counter or
    relationship to a halting equation, has a four-step exact evaluator. -/
theorem full_normalizer_one_left_four (y : Nat) :
    fullForcedNormalize 1 y = forcedFuel 4 (1,y) := by
  by_cases hy : y%2=1
  · have hnorm := full_normalizer_one_left_odd_one y hy
    rw [hnorm]
    have hterm := terminal_one_left_odd y hy
    cases h1 : forcedNext (1,y) with
    | none => simp [forcedFuel,h1]
    | some t =>
      have ht : forcedNext t = none := by
        simpa [forcedFuel,h1] using hterm
      simp [forcedFuel,h1,ht]
  · have he : y%2=0 := by omega
    exact full_normalizer_four_mass_one 1 y (by omega)

/-- The first genuine section stopping equation with even m lies
    in weighted-mass class one, hence has an exact four-step evaluator. -/
theorem first_stopping_even_m_four (m k : Nat)
    (hm : m%2=0)
    (hgate : k+3*m+4=2^(2*m+3)) :
    fullForcedNormalize 1 k = forcedFuel 4 (1,k) :=
  full_normalizer_one_left_four k

/-- The second stopping equation with even m necessarily has
    weighted mass one modulo four, independent of j. -/
theorem second_stopping_even_m_four (j m k : Nat)
    (hm : m%2=0)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    fullForcedNormalize (2*j+3) k = forcedFuel 4 (2*j+3,k) := by
  have hPdiv : 2∣2^(2*m+2) := by
    change 2^1∣2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨z,hz⟩ := hPdiv
  have hd : 2∣k+j+3*m+5 := by
    refine ⟨z*(j+3),?_⟩
    calc
      k+j+3*m+5 = 2^(2*m+2)*(j+3) := hgate
      _ = (2*z)*(j+3) := by rw [hz]
      _ = 2*(z*(j+3)) := by ac_rfl
  have hpar : (k+j+3*m+5)%2=0 := Nat.mod_eq_zero_of_dvd hd
  have hmass : ((2*j+3)+2*k)%4=1 := by omega
  exact full_normalizer_four_mass_one (2*j+3) k hmass

/-- Under the genuine second stopping equation, odd j and odd m
    require at most two exact source inverse returns. -/
private theorem terminal_second_oddodd (j m k : Nat)
    (hj : j%2=1) (hm : m%2=1)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    forcedNext (forcedFuel 2 (2*j+3,k)) = none := by
  cases h1 : forcedNext (2*j+3,k) with
  | none => simpa [forcedFuel,h1] using h1
  | some t =>
    cases h2 : forcedNext t with
    | none => simpa [forcedFuel,h1,h2] using h2
    | some u =>
      by_cases h3 : forcedNext u = none
      · simpa [forcedFuel,h1,h2] using h3
      · cases h3' : forcedNext u with
        | none => contradiction
        | some v =>
          exact False.elim (oddodd_second_gate_no_three j m k
            t.1 t.2 u.1 u.2 v.1 v.2 hj hm hgate
            (forcedNext_edge (2*j+3,k) t h1)
            (forcedNext_edge t u h2)
            (forcedNext_edge u v h3'))

theorem second_stopping_oddodd_two (j m k : Nat)
    (hj : j%2=1) (hm : m%2=1)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    fullForcedNormalize (2*j+3) k = forcedFuel 2 (2*j+3,k) :=
  forcedFuel_eq_norm_of_terminal 2 (2*j+3,k)
    (terminal_second_oddodd j m k hj hm hgate)

#print axioms full_normalizer_two_mass_two
#print axioms full_normalizer_one_left_four
#print axioms second_stopping_even_m_four
#print axioms second_stopping_oddodd_two

#print axioms full_normalizer_four_mass_one
#print axioms full_normalizer_five_mass_zero
end BB6.Agent29Depth
