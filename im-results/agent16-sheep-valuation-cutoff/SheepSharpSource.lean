import SheepEvenSourceAlgebra
import SheepPowerCutoff
import SpecialSourceNoPower

namespace SheepSharperSource
open SheepSharper

/-- For every genuine first-even edge into a power of two, the parent is
    necessarily generic and its source valuation satisfies the new bounds. -/
theorem original_power_generic_cutoffs {x j : Nat}
    (hx : x % 2 = 0) (edge : SheepEven.EvenEdge x (2^j)) :
    ∃ a h v u : Nat,
      1 ≤ a ∧ 5 ≤ v ∧ v % 2 = 1 ∧ u % 2 = 1 ∧
      x = 2^a*v ∧ 2^j = 1+3^h*u ∧
      (h < 15 ∨ a < cutoff h) ∧
      (h < 100 ∨ a < cutoffFive h) := by
  have hc := SheepEvenSourceAlgebra.even_edge_to_algebra hx edge
  rcases hc with hg | hs
  · obtain ⟨a,h,v,u,ha,hv,ho,hu,hx',hy,heq⟩ :=
      SheepEvenInverseAlgebra.generic_inverse_equation
        x (2^j) 1 j 0 hg (by simp)
    have heq' : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
        =2^(j+h+1)+3*3^h := by simpa using heq
    have hthree : h < 15 ∨ a < cutoff h := by
      by_contra hh
      have hh15 : 15 ≤ h := by omega
      have hcut : cutoff h ≤ a := by omega
      have a3 : 3 ≤ a := by
        have hmin : 30 ≤ cutoff h := by unfold cutoff; omega
        omega
      have eq := generic_source_diophantine a h v j a3 heq'
      exact (no_power_generic_three j h a v hh15 hcut) eq
    have hfive : h < 100 ∨ a < cutoffFive h := by
      by_contra hh
      have hh100 : 100 ≤ h := by omega
      have hcut : cutoffFive h ≤ a := by omega
      have a3 : 3 ≤ a := by
        have hmin : 168 ≤ cutoffFive h := by unfold cutoffFive; omega
        omega
      have eq := generic_source_diophantine a h v j a3 heq'
      exact (no_power_generic_five j h a v hh100 hcut) eq
    exact ⟨a,h,v,u,ha,hv,ho,hu,hx',hy,hthree,hfive⟩
  · obtain ⟨a,h,u,ha,hu,hx',hz,hy⟩ := hs
    have hfactor : 3*2^a+a+2=2^h*u := by omega
    exact False.elim ((Agent17SheepSpecial.special_no_even_power
      a h u j ha hfactor hu) hy.symm)

#print axioms original_power_generic_cutoffs
end SheepSharperSource
