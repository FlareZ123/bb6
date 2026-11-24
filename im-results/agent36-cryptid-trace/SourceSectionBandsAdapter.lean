import SectionBands
import SectionBandSeparation
import Lean.Elab.Tactic.Omega

namespace BB6.Agent36.SourceSectionBandsAdapter

open CryptidBoundary
open BB6.OneSided
open BB6.Agent26.GrowthBands
open BB6.Agent36.SectionBandSeparation

/-- The numeric phase-band measure of an arbitrary normalized source suffix. -/
def sourceMeasure (n : Nat) (v : List Bool) : BB6.Agent26.GrowthBands.Section :=
  ⟨n, (BB6.OneSided.trim v).length⟩

/-- Agent 32's exact GoodReturn inequalities instantiate the widened
Agent 36 Edge135 relation without any additional simulation assumptions. -/
theorem edge135_of_goodReturn {n n' : Nat} {v v' : List Bool}
    (hn : 5 ≤ n) (h : BB6.OneSided.GoodReturn n v n' v') :
    Edge135 (sourceMeasure n v) (sourceMeasure n' v') := by
  rcases h with ⟨_, hlo, hup⟩
  exact edge135_of_bounds hn hlo hup

/-- A ReturnWitness supplies a positive-time exact source return and the
corresponding widened phase-band edge. -/
theorem edge135_of_returnWitness {n : Nat} {v : List Bool}
    (hn : 5 ≤ n) (h : BB6.OneSided.ReturnWitness n v) :
    ∃ t n' v', 0 < t ∧
      CryptidBoundary.run t (BB6.OneSided.Section n v) =
        BB6.OneSided.Section n' v' ∧
      BB6.OneSided.head v' = false ∧
      Edge135 (sourceMeasure n v) (sourceMeasure n' v') := by
  rcases h with ⟨t, n', v', ht, hrun, hgood⟩
  rcases hgood with ⟨hv', hlo, hup⟩
  exact ⟨t, n', v', ht, hrun, hv', edge135_of_bounds hn hlo hup⟩

/-- The global arbitrary-suffix theorem is now in the exact form needed by
Path135: every normalized section either halts or supplies a positive-time
exact source return, a normalized successor suffix, and an Edge135 step. -/
theorem section_edge_or_halt {n : Nat} {v : List Bool}
    (hn : 5 ≤ n) (hv : BB6.OneSided.head v = false) :
    BB6.OneSided.HaltWitness n v ∨
      ∃ t n' v', 0 < t ∧
        CryptidBoundary.run t (BB6.OneSided.Section n v) =
          BB6.OneSided.Section n' v' ∧
        BB6.OneSided.head v' = false ∧
        Edge135 (sourceMeasure n v) (sourceMeasure n' v') := by
  rcases BB6.OneSided.section_bands n v (by omega) hv with hhalt | hreturn
  · exact Or.inl hhalt
  · exact Or.inr (edge135_of_returnWitness hn hreturn)

#print axioms edge135_of_goodReturn
#print axioms edge135_of_returnWitness
#print axioms section_edge_or_halt

end BB6.Agent36.SourceSectionBandsAdapter
