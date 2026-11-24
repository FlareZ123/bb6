import CompressedMemo

namespace BB6.Agent12KernelCone
open BB6.Agent12ValuationParents BB6.Agent12DirectJump BB6.Agent12CompressedMemo
open BB6.Agent13ExactMemo
abbrev P := Nat × Nat

/-- Unlike the full memoizer, this restricted checker has a structural
    reduction path. A nonexcluded small-right node is inconclusive. -/
def highParents (p : P) : List P :=
  if jumpGate p.1 p.2 then [jumpTarget p.1 p.2] else valuationParents p.1 p.2

def treeExcluded (cap : Nat) : Nat → P → Bool
  | 0,p => enhancedBad cap p
  | f+1,p => if enhancedBad cap p then true
             else if 8≤p.2 then (highParents p).all (treeExcluded cap f)
             else false

theorem treeExcluded_sound_of (cap : Nat) (reach : P → Prop)
    (parentLaw : ∀ p, 8≤p.2 → reach p → ∃ q ∈ highParents p, reach q)
    (badLaw : ∀ p, enhancedBad cap p = true → ¬ reach p)
    (f : Nat) (p : P) (h : treeExcluded cap f p = true) : ¬ reach p := by
  induction f generalizing p with
  | zero => exact badLaw p h
  | succ f ih =>
    by_cases hb : enhancedBad cap p = true
    · exact badLaw p hb
    have hbf : enhancedBad cap p = false := Bool.eq_false_iff.mpr hb
    by_cases hy : 8 ≤ p.2
    · have hall : (highParents p).all (treeExcluded cap f) = true := by
        simpa [treeExcluded,hbf,hy] using h
      intro hr
      obtain ⟨q,hq,hreach⟩ := parentLaw p hy hr
      exact ih q (List.all_eq_true.mp hall q hq) hreach
    · simp [treeExcluded,hbf,hy] at h

theorem treeExcluded_children (cap f : Nat) (p : P) (hy : 8≤p.2)
    (hc : ∀ q ∈ highParents p, treeExcluded cap f q = true) :
    treeExcluded cap (f+1) p = true := by
  by_cases hb : enhancedBad cap p = true
  · simp [treeExcluded,hb]
  · have hbf : enhancedBad cap p = false := Bool.eq_false_iff.mpr hb
    simp [treeExcluded,hbf,hy,List.all_eq_true.mpr hc]

theorem highParents_eq (p : P) (hy : 8≤p.2) :
    highParents p = compressedParents p := by
  simp [highParents,compressedParents,plainParents,hy]

theorem highParents_source (p : P) (hy : 8≤p.2) (hr : sourceReach p) :
    ∃ q ∈ highParents p, sourceReach q := by
  rcases (compressedReach_iff p).mp hr with h | ⟨q,hq,hrq⟩
  · rw [h] at hy
    omega
  · exact ⟨q,by rwa [highParents_eq p hy],hrq⟩

theorem treeExcluded_sound (cap f : Nat) (p : P)
    (h : treeExcluded cap f p = true) : ¬sourceReach p :=
  treeExcluded_sound_of cap sourceReach highParents_source (enhancedBad_sound cap) f p h

set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
theorem lowStop10_cert : treeExcluded 24 7 (1,8388574) = true := by decide +kernel

theorem lowStop10_not_reachable : ¬BB6.Agent3.CReach 1 8388574 :=
  treeExcluded_sound 24 7 (1,8388574) lowStop10_cert

#print axioms treeExcluded_sound_of
#print axioms treeExcluded_children
#print axioms treeExcluded_sound
#print axioms lowStop10_cert
#print axioms lowStop10_not_reachable
end BB6.Agent12KernelCone
