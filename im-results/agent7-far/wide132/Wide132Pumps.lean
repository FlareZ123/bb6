import BlockPump
import DepthEightFAR
namespace BB6.Agent7Wide132
open BB6Coverage BB6Coverage.FAR BB6Coverage.Agent50Pump
def p46 : PartialMachine := fromCodes [7,15,11,22,13,24,14,19,1,4,18,4]
def c46 : Certificate := ⟨30, ⟨0, word "10" "" "", word "10" "110110" "1100"⟩, List.replicate 2 Op.step ++ [.right 1 6 (bits "110110")] ++ List.replicate 35 Op.step ++ [.left 0 6 (bits "110110")] ++ List.replicate 6 Op.step ++ [.right 1 6 (bits "110110")] ++ List.replicate 13 Op.step ++ [.left 0 6 (bits "110110")] ++ List.replicate 4 Op.step⟩
theorem c46_checked : c46.check p46 = true := by decide
theorem p46_never (m : Machine) (hm : compatible p46 m) : NeverHalts m :=
  Certificate.never p46 c46 c46_checked m hm
#print axioms p46_never

def p150 : PartialMachine := fromCodes [7,24,11,22,13,9,14,19,10,4,0,4]
def c150 : Certificate := ⟨27, ⟨0, word "" "" "", word "010" "11111111" "11111"⟩, List.replicate 3 Op.step ++ [.right 2 32 (bits "11111111")] ++ List.replicate 34 Op.step ++ [.left 0 8 (bits "01010101")] ++ List.replicate 4 Op.step ++ [.right 1 12 (bits "00000000")] ++ List.replicate 29 Op.step ++ [.left 0 8 (bits "11111111")] ++ List.replicate 5 Op.step⟩
theorem c150_checked : c150.check p150 = true := by decide
theorem p150_never (m : Machine) (hm : compatible p150 m) : NeverHalts m :=
  Certificate.never p150 c150 c150_checked m hm
#print axioms p150_never

end BB6.Agent7Wide132
