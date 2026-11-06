import BB429SurvivorMask
import Lean.Elab.Tactic.Omega

namespace BB429SurvivorMask
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

theorem base58_nodup : base58.Nodup := by decide

/-- Each surviving residue lies in its unique 16384-sized quotient interval. -/
theorem block_range (j x : Nat) (hx : x ∈ survivorsAt j) :
    16384*j ≤ x ∧ x < 16384*(j+1) := by
  obtain ⟨hmap,_⟩ := List.mem_filter.mp hx
  obtain ⟨r,hr,heq⟩ := List.mem_map.mp hmap
  have hrlt : r<16384 := of_decide_eq_true
    ((List.all_eq_true.mp base58_small) r hr)
  omega

/-- Every source residue occurs at most once within each lifted block. -/
theorem block_nodup (j : Nat) : (survivorsAt j).Nodup := by
  unfold survivorsAt
  apply List.Pairwise.filter
  rw [List.pairwise_map]
  exact (List.nodup_iff_pairwise_ne.mp base58_nodup).imp (by
    intro a b hab
    omega)

/-- Left-associated prefix of the 16 disjoint lifted blocks. -/
def segments : Nat → List Nat
  | 0 => []
  | n+1 => segments n ++ survivorsAt n

theorem segments_good (n : Nat) :
    (segments n).Nodup ∧
      ∀ x, x ∈ segments n → x < 16384*n := by
  induction n with
  | zero => simp [segments]
  | succ n ih =>
    obtain ⟨hnd,hrng⟩ := ih
    constructor
    · change (segments n ++ survivorsAt n).Nodup
      apply List.nodup_append.mpr
      refine ⟨hnd,block_nodup n,?_⟩
      intro a ha b hb
      have hla := hrng a ha
      have hgb := (block_range n b hb).1
      omega
    · intro x hx
      change x ∈ segments n ++ survivorsAt n at hx
      rcases List.mem_append.mp hx with ha | hb
      · have hla := hrng x ha
        omega
      · have hr := (block_range n x hb).2
        omega

private theorem live255_eq_segments : live255 = segments 16 := by
  simp only [live255, segments, List.nil_append, List.append_assoc]

/-- The 255-element necessary gate consists of 255 distinct residue classes
    modulo 262144, with no duplicate contributions from the 16 blocks. -/
theorem live255_nodup : live255.Nodup := by
  rw [live255_eq_segments]
  exact (segments_good 16).1

theorem live255_exact_cardinality :
    live255.length = 255 ∧ live255.Nodup :=
  ⟨live255_count,live255_nodup⟩

#print axioms live255_nodup
#print axioms live255_exact_cardinality
end BB429SurvivorMask
