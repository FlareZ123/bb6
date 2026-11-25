import BlockPump

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent2Raw124ZeroLFBlockGrowth
open BB6Coverage BB6Coverage.Agent50Pump

def fromRows (xs : List (Option (Option Move))) : PartialMachine :=
  fun s => (xs[2*s.1.val+s.2.toNat]?).getD none

def p1539 : PartialMachine := fromRows [some (some ⟨true,true,1⟩),some (some ⟨false,true,4⟩),some (some ⟨true,true,2⟩),some (some ⟨true,true,0⟩),some (some ⟨false,true,3⟩),some (some ⟨false,true,1⟩),some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),none,some (some ⟨true,false,5⟩),some (some ⟨true,true,1⟩),some (some ⟨false,false,5⟩)]

def p1547 : PartialMachine := fromRows [some (some ⟨true,true,1⟩),some (some ⟨true,true,5⟩),some (some ⟨true,true,2⟩),some (some ⟨true,true,0⟩),some (some ⟨false,true,3⟩),some (some ⟨false,true,1⟩),some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),none,some (some ⟨true,false,5⟩),some (some ⟨true,true,1⟩),some (some ⟨false,false,5⟩)]

def shape1539 : Shape := ⟨0,word "0" "111011101110" "11101110111111",word "" "" ""⟩
def shape1547 : Shape := ⟨0,word "010" "11101110" "11101110111111",word "" "" ""⟩

def ops1539 : List Op := List.replicate 9 .step ++ [.left 0 36 (bits "001100110011")] ++ List.replicate 66 .step ++ [.right 1 12 (bits "011101110111")] ++ List.replicate 27 .step ++ [.left 3 36 (bits "001100110011")] ++ List.replicate 79 .step ++ [.right 1 12 (bits "011101110111")] ++ List.replicate 9 .step ++ [.rewrite shape1539.grow]
def ops1547 : List Op := List.replicate 19 .step ++ [.left 0 24 (bits "00110011")] ++ List.replicate 66 .step ++ [.right 1 8 (bits "01110111")] ++ List.replicate 21 .step ++ [.left 6 24 (bits "10011001")] ++ List.replicate 82 .step ++ [.right 1 8 (bits "11101110")] ++ List.replicate 2 .step

def c1539 : Certificate := ⟨91,shape1539,ops1539⟩
def c1547 : Certificate := ⟨155,shape1547,ops1547⟩

theorem check1539 : c1539.check p1539 = true := by decide
theorem check1547 : c1547.check p1547 = true := by decide

theorem never1539 : ∀ m, compatible p1539 m → NeverHalts m :=
  Certificate.never p1539 c1539 check1539

theorem never1547 : ∀ m, compatible p1547 m → NeverHalts m :=
  Certificate.never p1547 c1547 check1547

#print axioms never1539
#print axioms never1547
end BB6.Agent2Raw124ZeroLFBlockGrowth
