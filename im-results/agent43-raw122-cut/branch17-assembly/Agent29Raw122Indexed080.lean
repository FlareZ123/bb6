import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M080
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def t0_9 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,6⟩ .empty) ⟨0,false,0,17⟩ (.node .empty ⟨0,false,3,8⟩ .empty)) ⟨0,false,3,24⟩ (.node (.node (.node .empty ⟨0,false,7,0⟩ .empty) ⟨0,false,12,24⟩ .empty) ⟨0,false,12,27⟩ (.node .empty ⟨0,false,17,24⟩ .empty)))
def t10_18 : Tree := (.node (.node (.node (.node .empty ⟨0,true,1,14⟩ .empty) ⟨0,true,1,21⟩ .empty) ⟨0,true,5,6⟩ (.node .empty ⟨1,false,1,0⟩ .empty)) ⟨1,false,1,5⟩ (.node (.node .empty ⟨1,false,1,16⟩ .empty) ⟨1,false,8,0⟩ (.node .empty ⟨1,false,11,7⟩ .empty)))
def t0_18 : Tree := .node t0_9 ⟨0,false,17,27⟩ t10_18
def t19_27 : Tree := (.node (.node (.node (.node .empty ⟨1,false,11,23⟩ .empty) ⟨1,false,16,22⟩ .empty) ⟨1,false,16,23⟩ (.node .empty ⟨1,false,16,26⟩ .empty)) ⟨2,false,2,0⟩ (.node (.node .empty ⟨2,false,3,14⟩ .empty) ⟨2,false,3,21⟩ (.node .empty ⟨2,false,4,1⟩ .empty)))
def t28_36 : Tree := (.node (.node (.node (.node .empty ⟨2,false,9,0⟩ .empty) ⟨2,false,12,6⟩ .empty) ⟨2,false,13,13⟩ (.node .empty ⟨2,false,13,19⟩ .empty)) ⟨2,false,13,32⟩ (.node (.node .empty ⟨2,false,18,11⟩ .empty) ⟨2,false,18,13⟩ (.node .empty ⟨2,false,18,19⟩ .empty)))
def t19_36 : Tree := .node t19_27 ⟨2,false,4,19⟩ t28_36
def t0_36 : Tree := .node t0_18 ⟨1,false,11,22⟩ t19_36
def t37_46 : Tree := (.node (.node (.node (.node .empty ⟨2,false,18,32⟩ .empty) ⟨2,true,2,4⟩ .empty) ⟨2,true,2,15⟩ (.node .empty ⟨2,true,2,22⟩ .empty)) ⟨2,true,3,3⟩ (.node (.node (.node .empty ⟨2,true,3,21⟩ .empty) ⟨2,true,12,14⟩ .empty) ⟨2,true,12,21⟩ (.node .empty ⟨2,true,12,34⟩ .empty)))
def t47_55 : Tree := (.node (.node (.node (.node .empty ⟨2,true,17,21⟩ .empty) ⟨2,true,17,25⟩ .empty) ⟨2,true,17,34⟩ (.node .empty ⟨3,false,2,1⟩ .empty)) ⟨3,false,2,19⟩ (.node (.node .empty ⟨3,false,3,0⟩ .empty) ⟨3,false,3,18⟩ (.node .empty ⟨3,false,3,20⟩ .empty)))
def t37_55 : Tree := .node t37_46 ⟨2,true,17,14⟩ t47_55
def t56_64 : Tree := (.node (.node (.node (.node .empty ⟨3,false,4,19⟩ .empty) ⟨3,false,9,1⟩ .empty) ⟨3,false,10,0⟩ (.node .empty ⟨3,false,12,9⟩ .empty)) ⟨3,false,13,5⟩ (.node (.node .empty ⟨3,false,17,28⟩ .empty) ⟨3,false,18,10⟩ (.node .empty ⟨3,false,18,29⟩ .empty)))
def t65_73 : Tree := (.node (.node (.node (.node .empty ⟨3,false,19,28⟩ .empty) ⟨3,true,1,2⟩ .empty) ⟨3,true,1,20⟩ (.node .empty ⟨3,true,5,0⟩ .empty)) ⟨3,true,5,18⟩ (.node (.node .empty ⟨3,true,5,20⟩ .empty) ⟨3,true,5,33⟩ (.node .empty ⟨3,true,8,2⟩ .empty)))
def t56_73 : Tree := .node t56_64 ⟨3,false,19,9⟩ t65_73
def t37_73 : Tree := .node t37_55 ⟨3,false,4,13⟩ t56_73
def t0_73 : Tree := .node t0_36 ⟨2,false,18,30⟩ t37_73
def t74_83 : Tree := (.node (.node (.node (.node .empty ⟨3,true,14,12⟩ .empty) ⟨3,true,14,18⟩ .empty) ⟨3,true,14,20⟩ (.node .empty ⟨3,true,14,31⟩ .empty)) ⟨3,true,14,33⟩ (.node (.node (.node .empty ⟨3,true,16,29⟩ .empty) ⟨3,true,19,12⟩ .empty) ⟨3,true,19,18⟩ (.node .empty ⟨3,true,19,20⟩ .empty)))
def t84_92 : Tree := (.node (.node (.node (.node .empty ⟨3,true,19,33⟩ .empty) ⟨4,false,6,0⟩ .empty) ⟨4,true,2,1⟩ (.node .empty ⟨4,true,2,19⟩ .empty)) ⟨4,true,6,13⟩ (.node (.node .empty ⟨4,true,6,19⟩ .empty) ⟨4,true,6,32⟩ (.node .empty ⟨4,true,9,1⟩ .empty)))
def t74_92 : Tree := .node t74_83 ⟨3,true,19,31⟩ t84_92
def t93_101 : Tree := (.node (.node (.node (.node .empty ⟨4,true,15,11⟩ .empty) ⟨4,true,15,13⟩ .empty) ⟨4,true,15,19⟩ (.node .empty ⟨4,true,15,30⟩ .empty)) ⟨4,true,15,32⟩ (.node (.node .empty ⟨4,true,17,28⟩ .empty) ⟨5,false,0,5⟩ (.node .empty ⟨5,false,0,16⟩ .empty)))
def t102_110 : Tree := (.node (.node (.node (.node .empty ⟨5,false,2,19⟩ .empty) ⟨5,false,4,7⟩ .empty) ⟨5,false,4,22⟩ (.node .empty ⟨5,false,4,23⟩ .empty)) ⟨5,false,6,5⟩ (.node (.node .empty ⟨5,false,13,22⟩ .empty) ⟨5,false,13,23⟩ (.node .empty ⟨5,false,13,26⟩ .empty)))
def t93_110 : Tree := .node t93_101 ⟨5,false,2,13⟩ t102_110
def t74_110 : Tree := .node t74_92 ⟨4,true,12,9⟩ t93_110
def t111_119 : Tree := (.node (.node (.node (.node .empty ⟨5,false,18,23⟩ .empty) ⟨5,false,18,26⟩ .empty) ⟨5,true,0,4⟩ (.node .empty ⟨5,true,0,15⟩ .empty)) ⟨5,true,0,22⟩ (.node (.node .empty ⟨5,true,1,3⟩ .empty) ⟨5,true,1,21⟩ (.node .empty ⟨5,true,3,12⟩ .empty)))
def t120_128 : Tree := (.node (.node (.node (.node .empty ⟨5,true,3,33⟩ .empty) ⟨5,true,5,14⟩ .empty) ⟨5,true,5,21⟩ (.node .empty ⟨5,true,5,34⟩ .empty)) ⟨5,true,7,4⟩ (.node (.node .empty ⟨5,true,8,3⟩ .empty) ⟨5,true,11,11⟩ (.node .empty ⟨5,true,11,19⟩ .empty)))
def t111_128 : Tree := .node t111_119 ⟨5,true,3,20⟩ t120_128
def t129_137 : Tree := (.node (.node (.node (.node .empty ⟨5,true,12,20⟩ .empty) ⟨5,true,12,31⟩ .empty) ⟨5,true,12,33⟩ (.node .empty ⟨5,true,14,14⟩ .empty)) ⟨5,true,14,21⟩ (.node (.node .empty ⟨5,true,14,25⟩ .empty) ⟨5,true,14,34⟩ (.node .empty ⟨5,true,16,19⟩ .empty)))
def t138_146 : Tree := (.node (.node (.node (.node .empty ⟨5,true,16,32⟩ .empty) ⟨5,true,17,20⟩ .empty) ⟨5,true,17,31⟩ (.node .empty ⟨5,true,17,33⟩ .empty)) ⟨5,true,19,14⟩ (.node (.node .empty ⟨5,true,19,21⟩ .empty) ⟨5,true,19,25⟩ (.node .empty ⟨5,true,19,34⟩ .empty)))
def t129_146 : Tree := .node t129_137 ⟨5,true,16,30⟩ t138_146
def t111_146 : Tree := .node t111_128 ⟨5,true,11,32⟩ t129_146
def t74_146 : Tree := .node t74_110 ⟨5,false,18,22⟩ t111_146
def t0_146 : Tree := .node t0_73 ⟨3,true,11,10⟩ t74_146
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 0, 4, 11, 5, 0, 0, 6, 7, 0, 0, 8, 0, 9, 10, 0, 0, 0, 0, 12, 13, 16, 14, 0, 0, 15, 0, 0, 0, 17, 18, 16, 19, 0, 0, 15],#[0, 1, 3, 2, 0, 0, 0, 4, 0, 5, 6, 9, 7, 0, 8, 0, 0, 0, 11, 10, 0, 28, 25, 12, 0, 13, 14, 18, 15, 23, 0, 16, 17, 0, 0, 0, 0, 19, 21, 20, 0, 19, 15, 22, 24, 16, 24, 0, 0, 0, 0, 26, 27, 0, 0, 0, 30, 29, 0, 28, 25, 31, 0, 32, 34, 33, 0, 19, 0, 23],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,3)],[(false,4)],[(true,5)],[(false,6)],[(true,7)],[(true,8)],[(false,9)],[(true,3)],[(true,11)],[(false,12)],[(false,13)],[(true,14),(true,19)],[(true,12),(true,17)],[(true,16)],[(false,17)],[(false,18)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3)],[(true,4)],[(false,5)],[(false,6)],[(false,7)],[(true,5)],[(true,9)],[(false,9)],[(true,11)],[(true,12)],[(false,13)],[(false,14),(false,21)],[(true,15),(true,22)],[(false,16)],[(true,13)],[(true,18),(true,20),(true,33)],[(true,19)],[(false,19)],[(true,21)],[(true,14),(true,34)],[(false,22),(false,23)],[(false,11),(false,30)],[(true,25)],[(false,26)],[(true,10),(true,29)],[(true,28)],[(false,28)],[(true,30)],[(true,31)],[(true,32)],[(false,32)]],
  t0_146⟩
theorem check0_9 : t0_9.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check10_18 : t10_18.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node9 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,17,27⟩ = true := by decide
theorem check0_18 : t0_18.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node9 check0_9 check10_18
theorem check19_27 : t19_27.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check28_36 : t28_36.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node27 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,4,19⟩ = true := by decide
theorem check19_36 : t19_36.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node27 check19_27 check28_36
theorem node18 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,11,22⟩ = true := by decide
theorem check0_36 : t0_36.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node18 check0_18 check19_36
theorem check37_46 : t37_46.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check47_55 : t47_55.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node46 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,17,14⟩ = true := by decide
theorem check37_55 : t37_55.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node46 check37_46 check47_55
theorem check56_64 : t56_64.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check65_73 : t65_73.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node64 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,19,9⟩ = true := by decide
theorem check56_73 : t56_73.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node64 check56_64 check65_73
theorem node55 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,4,13⟩ = true := by decide
theorem check37_73 : t37_73.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node55 check37_55 check56_73
theorem node36 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,18,30⟩ = true := by decide
theorem check0_73 : t0_73.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node36 check0_36 check37_73
theorem check74_83 : t74_83.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check84_92 : t84_92.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node83 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,19,31⟩ = true := by decide
theorem check74_92 : t74_92.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node83 check74_83 check84_92
theorem check93_101 : t93_101.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check102_110 : t102_110.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node101 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,2,13⟩ = true := by decide
theorem check93_110 : t93_110.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node101 check93_101 check102_110
theorem node92 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,12,9⟩ = true := by decide
theorem check74_110 : t74_110.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node92 check74_92 check93_110
theorem check111_119 : t111_119.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check120_128 : t120_128.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node119 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,3,20⟩ = true := by decide
theorem check111_128 : t111_128.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node119 check111_119 check120_128
theorem check129_137 : t129_137.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check138_146 : t138_146.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node137 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,16,30⟩ = true := by decide
theorem check129_146 : t129_146.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node137 check129_137 check138_146
theorem node128 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,11,32⟩ = true := by decide
theorem check111_146 : t111_146.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node128 check111_128 check129_146
theorem node110 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,18,22⟩ = true := by decide
theorem check74_146 : t74_146.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node110 check74_110 check111_146
theorem node73 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,11,10⟩ = true := by decide
theorem check0_146 : t0_146.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node73 check0_73 check74_146
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_146
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M080
