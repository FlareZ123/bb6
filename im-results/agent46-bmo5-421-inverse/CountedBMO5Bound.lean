import CountedBMO5PairCoverage

namespace CountedBMO5Pair.Coverage

open Counted421 (arrivalCost score potential potential_edge potential_end bandPrefix_bound arrival_edge)

/-- The weight bound holds for every ancestry, including roots other than 1, 2, 3. -/
theorem universal_arrival_potential (x : Nat) :
    ∀ i r, x=Cap.lo i+r → r≤Cap.c i+2 → arrivalCost x≤potential i r := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro i r hx hr
    cases hp : Cap.predecessor x with
    | none => rw [arrivalCost,hp]; omega
    | some p =>
      have e := Cap.predecessor_sound hp
      have hg := Cap.edge_grows e
      rw [arrival_edge e]
      by_cases hge : 2≤p
      · obtain ⟨j,hlo,hhi⟩ := Cap.band_exists p hge
        let s := p-Cap.lo j
        have hps : p=Cap.lo j+s := by dsimp [s]; omega
        have hs : s≤Cap.c j+2 := by rw [Cap.lo_step] at hhi; dsimp [s]; omega
        have hprev := ih p hg j s hps hs
        have he : Cap.Edge (Cap.lo j+s) (Cap.lo i+r) := by rw [←hps,←hx]; exact e
        have hpot := potential_edge hs hr he
        rw [←hps] at hpot
        omega
      · have hf := Cap.edge_iff.mp e
        have hp1 : p=1 := by
          by_cases hz : p=0
          · subst p; simp [Cap.f] at hf
          · omega
        subst p
        have heq : x=5 := by simpa [Cap.f] using hf.symm
        subst x
        have hband : Cap.lo i≤5 ∧ 5<Cap.lo (i+1) := by rw [Cap.lo_step]; omega
        have hband0 : Cap.lo 0≤5 ∧ 5<Cap.lo (0+1) := by decide
        have hi := Cap.band_unique hband hband0
        subst i
        have hr3 : r=3 := by simp [Cap.lo] at hx; omega
        subst r
        rw [arrivalCost,Counted421.fastScore_eq]
        decide

/-- A root-independent bound on every terminal's complete weighted ancestry. -/
theorem W_upper (i : Nat) : W i≤800*(i+5)*4^i := by
  have he : Cap.halt i=Cap.lo i+(Cap.c i+1) := by unfold Cap.halt; omega
  have hp := universal_arrival_potential (Cap.halt i) i (Cap.c i+1) he (by omega)
  have hb := potential_end i (Cap.c i+1) (by omega)
  rw [←he] at hb
  have hf := bandPrefix_bound i
  unfold W
  omega

/-- Even the terminal section alone takes at least this many attempted instructions. -/
theorem W_lower (i : Nat) : 60*4^i≤W i := by
  have h := Counted421.resetCost_band i
  have hp : 2^i≤4^i := Nat.pow_le_pow_left (by decide) _
  unfold W
  rw [Counted421.score_terminal,Counted421.resetPrefix]
  omega

theorem halts421_iff (n : Nat) : BB6Coverage.HaltsAfter Counted421.Coverage.machine n ↔
    ∃ i, Cap.rootOf (Cap.halt i)=2 ∧ n+1=W i+8 := by
  rw [Counted421.Coverage.haltsAfter_iff_terminal]
  constructor <;> rintro ⟨i,hi,hn⟩ <;> exact ⟨i,hi,by unfold W at *; omega⟩

theorem decidedBelow421_iff (bound : Nat) :
    BB6Coverage.DecidedBelow bound Counted421.Coverage.machine ↔
    ∀ i, Cap.rootOf (Cap.halt i)=2 → W i+8≤bound :=
  decidedBelow_generic Counted421.Coverage.machine 2 8 bound (by decide) halts421_iff

def allThreeBelow (bound : Nat) : Prop :=
  BB6Coverage.DecidedBelow bound machine252 ∧
  BB6Coverage.DecidedBelow bound Counted421.Coverage.machine ∧
  BB6Coverage.DecidedBelow bound machine754

/-- A single exact root-sensitive weighted obligation for the three actual tables. -/
theorem allThreeBelow_iff (bound : Nat) : allThreeBelow bound ↔
    ∀ i, (Cap.rootOf (Cap.halt i)=1 → W i+3≤bound) ∧
         (Cap.rootOf (Cap.halt i)=2 → W i+8≤bound) ∧
         (Cap.rootOf (Cap.halt i)=3 → W i+18≤bound) := by
  unfold allThreeBelow
  rw [decidedBelow252_iff,decidedBelow421_iff,decidedBelow754_iff]
  constructor
  · rintro ⟨h1,h2,h3⟩ i; exact ⟨h1 i,h2 i,h3 i⟩
  · intro h; exact ⟨fun i=>(h i).1,fun i=>(h i).2.1,fun i=>(h i).2.2⟩

/-- Maximality requires excluding only roots at high terminal indices. -/
theorem allThreeBelow_of_tail_exclusion (bound L : Nat)
    (hb : 18+800*(L+5)*4^L≤bound)
    (ht : ∀ i, L<i → Cap.rootOf (Cap.halt i)≠1 ∧
                          Cap.rootOf (Cap.halt i)≠2 ∧
                          Cap.rootOf (Cap.halt i)≠3) :
    allThreeBelow bound := by
  apply (allThreeBelow_iff bound).mpr
  intro i
  by_cases hi : i≤L
  · have hw := W_upper i
    have h1 : 800*(i+5)≤800*(L+5) := by omega
    have h2 : 4^i≤4^L := Nat.pow_le_pow_right (by decide) hi
    have h3 := Nat.mul_le_mul h1 h2
    exact ⟨fun _=>by omega,fun _=>by omega,fun _=>by omega⟩
  · obtain ⟨h1,h2,h3⟩ := ht i (by omega)
    exact ⟨fun h=>False.elim (h1 h),fun h=>False.elim (h2 h),fun h=>False.elim (h3 h)⟩

/-- Conversely, sufficiently large terminal indices must be excluded by any exact upper bound. -/
theorem tail_exclusion_of_allThreeBelow {bound : Nat} (h : allThreeBelow bound) :
    ∀ i, bound<60*4^i → Cap.rootOf (Cap.halt i)≠1 ∧
                          Cap.rootOf (Cap.halt i)≠2 ∧
                          Cap.rootOf (Cap.halt i)≠3 := by
  intro i hi
  obtain ⟨h1,h2,h3⟩ := (allThreeBelow_iff bound).mp h i
  have hl := W_lower i
  exact ⟨fun hr=>by have := h1 hr; omega,fun hr=>by have := h2 hr; omega,fun hr=>by have := h3 hr; omega⟩

#print axioms universal_arrival_potential
#print axioms W_upper
#print axioms W_lower
#print axioms allThreeBelow_iff
#print axioms allThreeBelow_of_tail_exclusion
#print axioms tail_exclusion_of_allThreeBelow
end CountedBMO5Pair.Coverage
