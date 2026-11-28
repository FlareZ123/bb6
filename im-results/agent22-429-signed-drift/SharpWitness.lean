import SharpValuationFamily

namespace ValuationPacking

def sharp15Edge : Edge 15 where
  v := 1
  j := 2
  next := 1
  vpos := by decide
  vsmall := by decide
  jpos := by decide
  eqn := by decide

theorem sharp15_family_nodup :
    ([sharp15Edge].map (fun e => e.v)).Nodup := by simp

theorem sharp15_equality :
    15*([sharp15Edge].map (fun e => e.j)).sum = 2*15 := by decide

theorem sharp_constant_attained :
    ∃ es : List (Edge 15),
      (es.map (fun e => e.v)).Nodup ∧
      15*(es.map (fun e => e.j)).sum = 2*15 := by
  exact ⟨[sharp15Edge],sharp15_family_nodup,sharp15_equality⟩

#print axioms sharp_constant_attained
end ValuationPacking
