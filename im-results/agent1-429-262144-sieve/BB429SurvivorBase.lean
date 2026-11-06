import BB429SplitSieve
import Lean.Elab.Tactic.Omega

namespace BB429SurvivorMask
open BB429SplitSieve
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

/-- Source-matched previous 58 necessary terminal residues modulo 16384.
    Their prior genuine-raw-source theorem belongs to BB429Source58Sixteen. -/
def base58 : List Nat := [9, 337, 465, 765, 1097, 1141, 1673, 1789, 1973, 2057, 2165, 2385, 2513, 2685, 2897, 3081, 3145, 3189, 3281, 4169, 4341, 4661, 4733, 5045, 5457, 6141, 6345, 6389, 6709, 7093, 7817, 7933, 8061, 8757, 9041, 9425, 10441, 10449, 10705, 11089, 11601, 12157, 12213, 12405, 12489, 12497, 12533, 12925, 13137, 13309, 13321, 14205, 14409, 14901, 15101, 15357, 16009, 16381]

theorem base58_small :
    base58.all (fun r => decide (r<16384)) = true := by decide

/-- Each candidate block consists of original residue lifts not eliminated
    by the all-quotient 673-ray source-certified inverse certificate. -/
def survivorsAt (j : Nat) : List Nat :=
    (base58.map (fun r => 16384*j+r)).filter (fun r => decide (r ∉ excluded))

/-- Explicit grouping avoids a monolithic kernel-normalization of the entire
    262144-residue quotient space. -/
def live255 : List Nat := survivorsAt 0 ++ survivorsAt 1 ++ survivorsAt 2 ++ survivorsAt 3 ++ survivorsAt 4 ++ survivorsAt 5 ++ survivorsAt 6 ++ survivorsAt 7 ++ survivorsAt 8 ++ survivorsAt 9 ++ survivorsAt 10 ++ survivorsAt 11 ++ survivorsAt 12 ++ survivorsAt 13 ++ survivorsAt 14 ++ survivorsAt 15

private theorem live255_flat :
    live255 = (List.range 16).flatMap survivorsAt := by
  simp only [live255, List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append]

/-- Exact arithmetic characterization for every natural counter, with no
    finite-size or depth assumption: this is precisely the former necessary
    58/16384 gate intersected with the complement of the 673 exclusions. -/
theorem live255_iff (u : Nat) :
    u%262144 ∈ live255 ↔
      u%16384 ∈ base58 ∧ u%262144 ∉ excluded := by
  rw [live255_flat]
  have hmod : (u%262144)%16384=u%16384 := by omega
  constructor
  · intro h
    obtain ⟨j,hj,hmem⟩ := List.mem_flatMap.mp h
    have hjlt : j<16 := List.mem_range.mp hj
    obtain ⟨hmap,hnot⟩ := List.mem_filter.mp hmem
    obtain ⟨r,hr,heq⟩ := List.mem_map.mp hmap
    have hrlt : r<16384 := of_decide_eq_true
      ((List.all_eq_true.mp base58_small) r hr)
    have hr0 : (16384*j+r)%16384=r := by omega
    constructor
    · rw [← hmod, ← heq, hr0]
      exact hr
    · exact of_decide_eq_true hnot
  · rintro ⟨hr,hnot⟩
    let j := (u%262144)/16384
    have hj : j<16 := by dsimp [j]; omega
    have hzr : 16384*j+u%16384=u%262144 := by dsimp [j]; omega
    apply List.mem_flatMap.mpr
    refine ⟨j,List.mem_range.mpr hj,?_⟩
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_map.mpr
      exact ⟨u%16384,hr,hzr⟩
    · exact decide_eq_true hnot

#print axioms live255_iff
end BB429SurvivorMask
