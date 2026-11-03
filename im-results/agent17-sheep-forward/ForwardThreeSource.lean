import SheepSourceBridge
import ForwardThreeEdge

namespace BB6.Agent17Forward

/-- A real one-section edge for the exact published Sheep source constructor.
    The arbitrary source is synthetic and is not a claim about the blank orbit. -/
theorem three_power_source_edges (k r s N : Nat)
    (hr : r < 3^k) (hs : s < 3^k) :
    ∃ x y : Nat, N ≤ x ∧ x % 2 = 0 ∧ y % 2 = 0 ∧
      x % (3^k) = r ∧ y % (3^k) = s ∧
      SheepBridge.SectionNext x y := by
  obtain ⟨b,u,x,y,hb,hxn,hu,huodd,hu4,hx,hxpow,hy,hx2,hy2,hxr,hys⟩ :=
    three_power_all_edges k r s N hr hs
  refine ⟨x,y,hxn,hx2,hy2,hxr,hys,?_⟩
  rw [hy, hxpow]
  exact SheepBridge.SectionNext.general (2*b) u hu huodd

#print axioms three_power_source_edges
end BB6.Agent17Forward
