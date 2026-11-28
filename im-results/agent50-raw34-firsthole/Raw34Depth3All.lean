import Raw34Depth3Shard00
import Raw34Depth3Shard01
import Raw34Depth3Shard02
import Raw34Depth3Shard03
import Raw34Depth3Shard04
import Raw34Depth3Shard05
import Raw34Depth3Shard06
import Raw34Depth3Shard07
import Raw34Depth3Shard08
import Raw34Depth3Shard09
import Raw34Depth3Shard10
import Raw34Depth3Shard11
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50Raw34Depth3

def witnesses : List Witness :=
  Shard00.witnesses ++
  Shard01.witnesses ++
  Shard02.witnesses ++
  Shard03.witnesses ++
  Shard04.witnesses ++
  Shard05.witnesses ++
  Shard06.witnesses ++
  Shard07.witnesses ++
  Shard08.witnesses ++
  Shard09.witnesses ++
  Shard10.witnesses ++
  Shard11.witnesses

theorem witness_count : witnesses.length = 1206 := by
  simp only [witnesses,List.length_append,Shard00.count,Shard01.count,Shard02.count,Shard03.count,Shard04.count,Shard05.count,Shard06.count,Shard07.count,Shard08.count,Shard09.count,Shard10.count,Shard11.count]
  omega

theorem all_checked : witnesses.all check = true := by
  simp [witnesses,List.all_append,Shard00.checked,Shard01.checked,Shard02.checked,Shard03.checked,Shard04.checked,Shard05.checked,Shard06.checked,Shard07.checked,Shard08.checked,Shard09.checked,Shard10.checked,Shard11.checked]

theorem all_never (w : Witness) (hw : w ∈ witnesses)
    (m : Machine) (hm : compatible (table w) m) : NeverHalts m :=
  check_sound w (List.all_eq_true.mp all_checked w hw) m hm

#print axioms witness_count
#print axioms all_checked
#print axioms all_never
end BB6.Agent50Raw34Depth3
