import Raw119Counter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw119Counter
open BB6Coverage BB6Coverage.Agent31Pump
namespace M5619
def pt : PartialMachine := table .erase (none)
def family (n : Nat) : Z0 := E (0+n) [] []
def cost (n : Nat) : Nat := (costs .erase (0+n)).2 0
theorem entry : run0 pt 31 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem epoch (n : Nat) : run0 pt (cost n) (family n) = some (family (n+1)) := growth .erase (none) (0+n) []
theorem positive (n : Nat) : 0 < cost n := advance_pos .erase (0+n) 0
theorem never (m : Machine) (hm : compatible pt m) : NeverHalts m :=
  never_of_growth pt family 31 cost entry positive epoch m hm
#print axioms never
end M5619

namespace M5750
def pt : PartialMachine := table .bounce (none)
def family (n : Nat) : Z0 := E (0+n) [] []
def cost (n : Nat) : Nat := (costs .bounce (0+n)).2 0
theorem entry : run0 pt 29 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem epoch (n : Nat) : run0 pt (cost n) (family n) = some (family (n+1)) := growth .bounce (none) (0+n) []
theorem positive (n : Nat) : 0 < cost n := advance_pos .bounce (0+n) 0
theorem never (m : Machine) (hm : compatible pt m) : NeverHalts m :=
  never_of_growth pt family 29 cost entry positive epoch m hm
#print axioms never
end M5750

namespace M5751
def pt : PartialMachine := table .plain (some (some ⟨false,false,0⟩))
def family (n : Nat) : Z0 := E (4+n) [] []
def cost (n : Nat) : Nat := (costs .plain (4+n)).2 0
theorem entry : run0 pt 88 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem epoch (n : Nat) : run0 pt (cost n) (family n) = some (family (n+1)) := growth .plain (some (some ⟨false,false,0⟩)) (4+n) []
theorem positive (n : Nat) : 0 < cost n := advance_pos .plain (4+n) 0
theorem never (m : Machine) (hm : compatible pt m) : NeverHalts m :=
  never_of_growth pt family 88 cost entry positive epoch m hm
#print axioms never
end M5751

namespace M5752
def pt : PartialMachine := table .plain (some (some ⟨false,false,4⟩))
def family (n : Nat) : Z0 := E (2+n) [] []
def cost (n : Nat) : Nat := (costs .plain (2+n)).2 0
theorem entry : run0 pt 76 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem epoch (n : Nat) : run0 pt (cost n) (family n) = some (family (n+1)) := growth .plain (some (some ⟨false,false,4⟩)) (2+n) []
theorem positive (n : Nat) : 0 < cost n := advance_pos .plain (2+n) 0
theorem never (m : Machine) (hm : compatible pt m) : NeverHalts m :=
  never_of_growth pt family 76 cost entry positive epoch m hm
#print axioms never
end M5752

namespace M5753
def pt : PartialMachine := table .plain (some (some ⟨false,false,5⟩))
def family (n : Nat) : Z0 := E (0+n) [true,true,true,true,true,false] []
def cost (n : Nat) : Nat := (costs .plain (0+n)).2 0
theorem entry : run0 pt 80 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem epoch (n : Nat) : run0 pt (cost n) (family n) = some (family (n+1)) := growth .plain (some (some ⟨false,false,5⟩)) (0+n) [true,true,true,true,true,false]
theorem positive (n : Nat) : 0 < cost n := advance_pos .plain (0+n) 0
theorem never (m : Machine) (hm : compatible pt m) : NeverHalts m :=
  never_of_growth pt family 80 cost entry positive epoch m hm
#print axioms never
end M5753

namespace M5754
def pt : PartialMachine := table .plain (some (some ⟨false,true,5⟩))
def family (n : Nat) : Z0 := E (0+n) [true,true,true,true,true,false] []
def cost (n : Nat) : Nat := (costs .plain (0+n)).2 0
theorem entry : run0 pt 82 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem epoch (n : Nat) : run0 pt (cost n) (family n) = some (family (n+1)) := growth .plain (some (some ⟨false,true,5⟩)) (0+n) [true,true,true,true,true,false]
theorem positive (n : Nat) : 0 < cost n := advance_pos .plain (0+n) 0
theorem never (m : Machine) (hm : compatible pt m) : NeverHalts m :=
  never_of_growth pt family 82 cost entry positive epoch m hm
#print axioms never
end M5754

namespace M5755
def pt : PartialMachine := table .plain (some (some ⟨true,true,0⟩))
def family (n : Nat) : Z0 := E (1+n) [true,true,true,true,true,false] []
def cost (n : Nat) : Nat := (costs .plain (1+n)).2 0
theorem entry : run0 pt 81 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem epoch (n : Nat) : run0 pt (cost n) (family n) = some (family (n+1)) := growth .plain (some (some ⟨true,true,0⟩)) (1+n) [true,true,true,true,true,false]
theorem positive (n : Nat) : 0 < cost n := advance_pos .plain (1+n) 0
theorem never (m : Machine) (hm : compatible pt m) : NeverHalts m :=
  never_of_growth pt family 81 cost entry positive epoch m hm
#print axioms never
end M5755

namespace M5756
def pt : PartialMachine := table .plain (some (some ⟨true,true,1⟩))
def family (n : Nat) : Z0 := E (0+n) [true,true,true,true,true,false] []
def cost (n : Nat) : Nat := (costs .plain (0+n)).2 0
theorem entry : run0 pt 78 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem epoch (n : Nat) : run0 pt (cost n) (family n) = some (family (n+1)) := growth .plain (some (some ⟨true,true,1⟩)) (0+n) [true,true,true,true,true,false]
theorem positive (n : Nat) : 0 < cost n := advance_pos .plain (0+n) 0
theorem never (m : Machine) (hm : compatible pt m) : NeverHalts m :=
  never_of_growth pt family 78 cost entry positive epoch m hm
#print axioms never
end M5756

namespace M5757
def pt : PartialMachine := table .plain (some (some ⟨true,true,5⟩))
def family (n : Nat) : Z0 := E (1+n) [true,true,true,true,true,false] []
def cost (n : Nat) : Nat := (costs .plain (1+n)).2 0
theorem entry : run0 pt 83 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem epoch (n : Nat) : run0 pt (cost n) (family n) = some (family (n+1)) := growth .plain (some (some ⟨true,true,5⟩)) (1+n) [true,true,true,true,true,false]
theorem positive (n : Nat) : 0 < cost n := advance_pos .plain (1+n) 0
theorem never (m : Machine) (hm : compatible pt m) : NeverHalts m :=
  never_of_growth pt family 83 cost entry positive epoch m hm
#print axioms never
end M5757
end BB6.Agent8Raw119Counter
