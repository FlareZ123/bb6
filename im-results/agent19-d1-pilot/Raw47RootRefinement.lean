import Raw47Cut
import RootFrontier

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent19Raw47RootRefinement
open BB6Coverage
open BB6.Agent19Raw47Cut
open BB6.Agent19CanonicalPartial
open BB6.Agent50RootFrontier

/-- The exact ordinary branch address from the firstOne root to Raw47:
    B0=1RC, C0=0RD, D0=1LD, D1=0RC. -/
def raw47Address : List Move :=
  [⟨true,true,2⟩, ⟨false,true,3⟩, ⟨true,false,3⟩, ⟨false,true,2⟩]

/-- Raw47 is one of Agent 50's 207 concrete firstOne root residuals. -/
theorem raw47_is_root_residual :
    (raw47Address, parent) ∈ residuals rootFrontier := by decide

/-- Replace the single concrete Raw47 leaf by its 114 canonical quotient
    residuals, retaining every other concrete root-frontier leaf. -/
theorem root_refined_sound :
    ∀ m, compatible root m →
      WeightedBound 84 m ∨
        (∃ a q, (a,q) ∈ residuals rootFrontier ∧
          (a,q) ≠ (raw47Address, parent) ∧ compatible q m) ∨
        (∃ e ∈ canonicalRemaining, TNFQuotientCompatible e.2 m) := by
  intro m hm
  rcases rootFrontier_sound m hm with hbound | ⟨a,q,hopen,hcomp⟩
  · exact Or.inl hbound
  · have hmem : (a,q) ∈ residuals rootFrontier := hopen.mem_residuals
    by_cases heq : (a,q) = (raw47Address, parent)
    · have hq : q = parent := congrArg Prod.snd heq
      have hcomp' : compatible parent m := by simpa [hq] using hcomp
      rcases canonical_local_sound_84 m (compatible_quotient hcomp') with hbound | hres
      · exact Or.inl hbound
      · exact Or.inr (Or.inr hres)
    · exact Or.inr (Or.inl ⟨a,q,hmem,heq,hcomp⟩)

#print axioms raw47_is_root_residual
#print axioms root_refined_sound
end BB6.Agent19Raw47RootRefinement
