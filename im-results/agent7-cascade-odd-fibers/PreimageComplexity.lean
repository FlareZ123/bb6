import PreimageCandidates

namespace CascadeSource

/-- The complete syntactic predecessor pool grows logarithmically with the
    target's first counter. This count is exact even when candidate entries
    duplicate or fail the exact Cstep-edge filter. -/
theorem candidate_exact_length (u v : Nat) :
    (preimageCandidates u v).length = 3 + 2*(Nat.log2 (u+2)+1) := by
  have hsum : ∀ l : List Nat, (l.map (fun _ => 2)).sum = 2*l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons a as ih => simp [ih]; omega
  simp [preimageCandidates,smallPreimages,oddPreimages,List.length_flatMap,hsum]
  omega

#print axioms candidate_exact_length

end CascadeSource
