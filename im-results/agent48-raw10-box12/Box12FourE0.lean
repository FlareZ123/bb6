import Box12E0
import Box12E3
import Box12E12
import Box12E18

namespace BB6.Agent48Box12
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49BoxBridge
open BB6.Agent49Box (Fits)
open BB6.Agent49Box6 (fromCodes decode partialEq_sound)

theorem fourE0Bound (B : Nat) (hB : 205 ≤ B) (m : Machine)
    (hm : Fits raw10Remainder[12]! m)
    (hE : m (4,false) ∈ [decode 0,decode 3,decode 12,decode 18]) : WeightedBound B m := by
  have hbase := sourceMatch_sound _ sourceIndex12 m hm
  have hp := initial_compatible m hbase
  apply ordinary_weighted B 200 hB m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hE
  rcases hE with h|h|h|h
  · apply node0 m hbase
    have hr := compatible_refine initial m (4,false) hp
    rw [h] at hr
    exact (show refine initial (4,false) (decode 0) = fromCodes #[8,25,11,11,17,13,11,25,0,25,25,25] from partialEq_sound (by decide +kernel)) ▸ hr
  · apply node1 m hbase
    have hr := compatible_refine initial m (4,false) hp
    rw [h] at hr
    exact (show refine initial (4,false) (decode 3) = fromCodes #[8,25,11,11,17,13,11,25,3,25,25,25] from partialEq_sound (by decide +kernel)) ▸ hr
  · apply e12 m hbase
    have hr := compatible_refine initial m (4,false) hp
    rw [h] at hr
    exact (show refine initial (4,false) (decode 12) = fromCodes #[8,25,11,11,17,13,11,25,12,25,25,25] from partialEq_sound (by decide +kernel)) ▸ hr
  · apply e18 m hbase
    have hr := compatible_refine initial m (4,false) hp
    rw [h] at hr
    exact (show refine initial (4,false) (decode 18) = fromCodes #[8,25,11,11,17,13,11,25,18,25,25,25] from partialEq_sound (by decide +kernel)) ▸ hr

#print axioms fourE0Bound
end BB6.Agent48Box12
