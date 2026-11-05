import DirectAncestry
import FastSectionDef
import Lean.Elab.Tactic.Omega

namespace BB6.Agent47Direct

private theorem machine_direct (x k:Nat) (hk:0<k) :
    BB6.Agent46.secNext (x+2*k,k) = some (x,2*k+2) := by
  have ha0 : x+2*k≠0 := by omega
  have ha1 : x+2*k≠1 := by omega
  have hk0 : k≠0 := by omega
  have hle : 2*k ≤ x+2*k := by omega
  simp [BB6.Agent46.secNext,BB6.Agent46.exactSection,
    ha0,ha1,hk0,hle,Nat.add_sub_cancel_left]
  have hbad : ¬ (x=0 ∧ 2*k=0) := by omega
  simp [hbad]

/-- Arbitrarily deep genuine Machine C section inverse paths to dyadic targets. -/
theorem source_long_chain (r u x:Nat) (hu:4≤u) :
    ∃ s, Chain BB6.Agent46.secNext r s (x,2^r*u-2) :=
  abstract_long_chain BB6.Agent46.secNext machine_direct r u x hu

#print axioms source_long_chain
end BB6.Agent47Direct
