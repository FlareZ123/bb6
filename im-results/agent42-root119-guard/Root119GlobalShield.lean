import Root119BRegular

namespace BB6Root119

/-- A physical 1100 word entirely to the left of or ending immediately
    before the live head. The existential permits arbitrary distance. -/
def HasLeft1100 (c : Conf) : Prop :=
  ∃ x : Int, x + 4 ≤ c.h ∧
    c.tape x = true ∧ c.tape (x+1) = true ∧
    c.tape (x+2) = false ∧ c.tape (x+3) = false

/-- The entire regular B/0 fatal corridor forces an unrestricted left-1100 factor. -/
theorem BBad_implies_left1100 (b : Conf) (hb : BBad b) :
    BZero b ∧ HasLeft1100 b := by
  obtain ⟨hB, r, hones, hzero, hzero2, hone3, hone4⟩ := hb
  refine ⟨hB, b.h-4-(r:Int), by omega, ?_, ?_, ?_, ?_⟩
  · have hpos : b.h-4-(r:Int)=b.h-4-(r:Int) := rfl
    exact hone4
  · have heq : (b.h-4-(r:Int))+1 = b.h-3-(r:Int) := by omega
    rw [heq]
    exact hone3
  · have heq : (b.h-4-(r:Int))+2 = b.h-2-(r:Int) := by omega
    rw [heq]
    exact hzero2
  · have heq : (b.h-4-(r:Int))+3 = b.h-1-(r:Int) := by omega
    rw [heq]
    exact hzero

/-- An inductively established safe left-half-tape language at genuine
    B/0 entries is enough to settle this auxiliary blank root. -/
theorem all_reached_B_zero_shield_implies_nonhalt
    (safe : ∀ b : Conf, Reach b → BZero b → ¬ HasLeft1100 b) :
    ¬ (∃ a, Reach a ∧ next a = none) := by
  intro halt
  obtain ⟨b, hb, hbad⟩ := blank_halts_iff_regular_B_gate.mp halt
  obtain ⟨hB, hfactor⟩ := BBad_implies_left1100 b hbad
  exact safe b hb hB hfactor

#print axioms BB6Root119.BBad_implies_left1100
#print axioms BB6Root119.all_reached_B_zero_shield_implies_nonhalt
end BB6Root119
