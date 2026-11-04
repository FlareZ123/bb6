import WellInverseCases

namespace CascadeSource

set_option maxHeartbeats 30000

/-- Candidate predecessors include three low-phase forms and at most
two power-of-two sweep forms per exponent. The list is intentionally
an overapproximation: exact edges are filtered with Cstep afterward. -/
def smallPreimages (u v : Nat) : List (Nat × Nat) :=
  [((v-1)/2,0), (0,2), ((4*u+v-8)/6,2)]

def oddPreimages (u v : Nat) : List (Nat × Nat) :=
  (List.range (Nat.log2 (u+2)+1)).flatMap (fun m =>
    let a := 4*2^m-2
    [(a,u+v), (a,4*u+v-6*a-3)])

def preimageCandidates (u v : Nat) : List (Nat × Nat) :=
  smallPreimages u v ++ oddPreimages u v

/-- Every predecessor in the root-invariant phase language occurs
in an explicitly computable logarithmic-length candidate list. -/
theorem source_well_preimage_complete (a b u v : Nat)
    (hw : WellState a b) (he : Cstep a b = some (u,v)) :
    (a,b) ∈ preimageCandidates u v := by
  rcases source_well_inverse_cases a b u v hw he with h0 | h2a | h2b | ⟨m,ha,hodd,hb3,hs⟩
  · rcases h0 with ⟨hb,hu,hv⟩
    apply List.mem_append.mpr
    left
    simp only [smallPreimages, List.mem_cons, List.not_mem_nil, or_false]
    left
    apply Prod.ext <;> omega
  · rcases h2a with ⟨hb,ha,hu,hv⟩
    apply List.mem_append.mpr
    left
    simp only [smallPreimages, List.mem_cons, List.not_mem_nil, or_false]
    right; left
    apply Prod.ext <;> omega
  · rcases h2b with ⟨hb,ha,heq,hv⟩
    apply List.mem_append.mpr
    left
    simp only [smallPreimages, List.mem_cons, List.not_mem_nil, or_false]
    right;right
    apply Prod.ext <;> omega
  · have hmem (hp : 2^m≤u+2) : m ∈ List.range (Nat.log2 (u+2)+1) := by
      apply List.mem_range.mpr
      have hn : u+2≠0 := by omega
      have hl : m ≤ Nat.log2 (u+2) := (Nat.le_log2 hn).mpr hp
      omega
    apply List.mem_append.mpr
    right
    apply List.mem_flatMap.mpr
    rcases hs with hlarge | hsmall
    · rcases hlarge with ⟨hu,hb,hv⟩
      have hp : 2^m ≤u+2 := by omega
      refine ⟨m,hmem hp,?_⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      left
      apply Prod.ext <;> omega
    · rcases hsmall with ⟨heq,hv,hsmall,hp⟩
      refine ⟨m,hmem hp,?_⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      right
      apply Prod.ext <;> omega

#print axioms source_well_preimage_complete

end CascadeSource
