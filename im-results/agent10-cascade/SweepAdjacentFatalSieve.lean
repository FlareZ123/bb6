import SweepOddFatalExceptional

namespace CascadeFastReturn
open CascadeBitSweep

/-- Two consecutive adjacent level-exit episodes, ending with an even
    fatal edge. The first edge's parity is deliberately left unspecified. -/
def EvenFinalAdjacentHistory (j m : Nat) : Prop :=
  ∃a e z v, firstFailIndex a=j ∧ bitOutcome a=some e ∧
    firstFailIndex e=j+1 ∧ SameLevelPath (j+1) e z m ∧
    bitOutcome z=some v ∧ (z+(j+1))%2=0 ∧
    firstFailIndex v=j+2 ∧ fatalAt v

/-- High-level adjacent predecessor of a successful even fatal exit is forced
    to be odd: source-level synthesis with the no-two-even theorem. -/
theorem even_final_adjacent_to_odd_entry (j m : Nat)
    (hj : 7≤j) (hh : EvenFinalAdjacentHistory j m) :
    OddFatalHistory (j+1) m := by
  obtain ⟨a,e,z,v,ha,hax,hx,hpath,hz,hzeven,hv,hfatal⟩ := hh
  have haodd : (a+j)%2=1 := by
    by_cases haeven : (a+j)%2=0
    · exact False.elim (no_consecutive_even_level_exits j a e z v m
        hj ha hax haeven hx hpath hz hzeven hv)
    · omega
  have haodd' : (a+firstFailIndex a)%2=1 := by rw [ha]; exact haodd
  have hv' : firstFailIndex v=(j+1)+1 := by omega
  exact ⟨a,e,z,v,haodd',hax,hx,hpath,hz,hv',hfatal⟩

/-- For two high-level adjacent-predecessor histories ending in even fatal
    exits at the same target level, the shorter depth is in the unique mod-6
    class. Source odd entry is now a derived condition. -/
theorem earlier_even_final_adjacent_depth_residue (j m₁ m₂ : Nat)
    (hj : 7≤j) (hlt : m₁<m₂)
    (h₁ : EvenFinalAdjacentHistory j m₁)
    (h₂ : EvenFinalAdjacentHistory j m₂) :
    ((j+1)%18=3∧m₁%6=5)∨((j+1)%18=4∧m₁%6=5)∨
    ((j+1)%18=9∧m₁%6=3)∨((j+1)%18=10∧m₁%6=1)∨
    ((j+1)%18=15∧m₁%6=1)∨((j+1)%18=16∧m₁%6=3) := by
  exact earlier_odd_fatal_depth_residue (j+1) m₁ m₂ hlt
    (even_final_adjacent_to_odd_entry j m₁ hj h₁)
    (even_final_adjacent_to_odd_entry j m₂ hj h₂)

#print axioms even_final_adjacent_to_odd_entry
#print axioms earlier_even_final_adjacent_depth_residue
end CascadeFastReturn
