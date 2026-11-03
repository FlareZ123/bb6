import SourceMacro

namespace CascadeSource

/-- Every completed source-indexed C episode strictly increases 2a+b. -/
theorem Cstep_mass_strict (a b u v : Nat)
    (he : Cstep a b = some (u,v)) : 2*a+b < 2*u+v := by
  rcases b with _ | _ | d
  · simp only [Cstep] at he
    rcases he with ⟨rfl,rfl⟩
    omega
  · simp [Cstep] at he
  · have hzero : d+2 ≠ 0 := by omega
    have hone : d+2 ≠ 1 := by omega
    by_cases hbig : 2*a ≤ d
    · have he' : some (2*a+2,d-2*a) = some (u,v) := by
        simpa [Cstep,hzero,hone,hbig] using he
      have hu : u=2*a+2 ∧ v=d-2*a := by simpa using he'.symm
      rcases hu with ⟨rfl,rfl⟩
      omega
    · let t:=6*a+d+(if d%2=0 then 8 else 5)
      have he' : some (t/4,t%4) = some (u,v) := by
        simpa [Cstep,hzero,hone,hbig,t] using he
      have hu : u=t/4 ∧ v=t%4 := by simpa using he'.symm
      rcases hu with ⟨rfl,rfl⟩
      have hsmall : d < 2*a := by omega
      have ht_even : t%2=0 := by
        dsimp [t]
        by_cases hd : d%2=0
        · simp only [if_pos hd]; omega
        · simp only [if_neg hd]; omega
      have ht_big : 2*(2*a+d+2) < t := by
        dsimp [t]
        by_cases hd : d%2=0
        · simp only [if_pos hd]; omega
        · simp only [if_neg hd]; omega
      have hmod : t%4=0 ∨ t%4=2 := by omega
      have hdiv : t=4*(t/4)+t%4 := by omega
      omega

inductive Orbit : (Nat × Nat) → (Nat × Nat) → Prop where
  | refl (x : Nat × Nat) : Orbit x x
  | step {a b c d u v : Nat} :
      Cstep a b = some (c,d) → Orbit (c,d) (u,v) → Orbit (a,b) (u,v)

def mass (x : Nat × Nat) : Nat := 2*x.1+x.2

/-- Arbitrarily many successful C episodes never decrease the weighted mass. -/
theorem orbit_mass_mono {x y : Nat × Nat} (h : Orbit x y) : mass x ≤ mass y := by
  induction h with
  | refl => omega
  | step hstep htail ih =>
    have hstrict := Cstep_mass_strict _ _ _ _ hstep
    dsimp [mass] at ih ⊢
    omega

/-- A strict mass crossing excludes a chosen reset forever in the compressed source. -/
theorem future_target_exclusion (a b t : Nat)
    (hbound : 2*t < 2*a+b) :
    ¬Orbit (a,b) (t,0) := by
  intro h
  have hm := orbit_mass_mono h
  dsimp [mass] at hm
  omega

#print axioms Cstep_mass_strict
#print axioms orbit_mass_mono
#print axioms future_target_exclusion

end CascadeSource
