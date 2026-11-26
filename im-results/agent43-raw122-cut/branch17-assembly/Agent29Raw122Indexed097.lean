import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M097
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def t0_9 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,true,1,4⟩ .empty) ⟨0,true,1,8⟩ (.node .empty ⟨0,true,1,9⟩ .empty)) ⟨0,true,6,0⟩ (.node (.node (.node .empty ⟨0,true,6,6⟩ .empty) ⟨0,true,6,9⟩ .empty) ⟨0,true,6,15⟩ (.node .empty ⟨1,false,0,6⟩ .empty)))
def t10_18 : Tree := (.node (.node (.node (.node .empty ⟨1,true,0,3⟩ .empty) ⟨1,true,0,14⟩ .empty) ⟨1,true,1,4⟩ (.node .empty ⟨1,true,1,8⟩ .empty)) ⟨2,false,1,3⟩ (.node (.node .empty ⟨2,false,1,14⟩ .empty) ⟨2,false,1,17⟩ (.node .empty ⟨2,false,2,0⟩ .empty)))
def t0_18 : Tree := .node t0_9 ⟨1,false,1,0⟩ t10_18
def t19_27 : Tree := (.node (.node (.node (.node .empty ⟨2,false,2,5⟩ .empty) ⟨2,false,2,12⟩ .empty) ⟨2,false,2,13⟩ (.node .empty ⟨2,false,2,16⟩ .empty)) ⟨2,false,7,0⟩ (.node (.node .empty ⟨2,false,7,2⟩ .empty) ⟨2,false,7,3⟩ (.node .empty ⟨2,false,7,5⟩ .empty)))
def t28_36 : Tree := (.node (.node (.node (.node .empty ⟨2,false,7,12⟩ .empty) ⟨2,false,7,13⟩ .empty) ⟨2,false,7,14⟩ (.node .empty ⟨2,false,7,16⟩ .empty)) ⟨2,false,7,17⟩ (.node (.node .empty ⟨2,true,2,3⟩ .empty) ⟨2,true,2,5⟩ (.node .empty ⟨2,true,2,12⟩ .empty)))
def t19_36 : Tree := .node t19_27 ⟨2,false,7,9⟩ t28_36
def t0_36 : Tree := .node t0_18 ⟨2,false,2,2⟩ t19_36
def t37_46 : Tree := (.node (.node (.node (.node .empty ⟨3,false,1,2⟩ .empty) ⟨3,false,1,5⟩ .empty) ⟨3,false,1,13⟩ (.node .empty ⟨3,false,1,16⟩ .empty)) ⟨3,false,2,1⟩ (.node (.node (.node .empty ⟨3,false,3,0⟩ .empty) ⟨3,false,4,1⟩ .empty) ⟨3,false,4,4⟩ (.node .empty ⟨3,false,4,7⟩ .empty)))
def t47_55 : Tree := (.node (.node (.node (.node .empty ⟨3,false,7,1⟩ .empty) ⟨3,false,7,2⟩ .empty) ⟨3,false,7,5⟩ (.node .empty ⟨3,false,7,7⟩ .empty)) ⟨3,false,7,8⟩ (.node (.node .empty ⟨3,false,7,13⟩ .empty) ⟨3,false,7,16⟩ (.node .empty ⟨3,false,8,0⟩ .empty)))
def t37_55 : Tree := .node t37_46 ⟨3,false,4,8⟩ t47_55
def t56_64 : Tree := (.node (.node (.node (.node .empty ⟨3,false,8,2⟩ .empty) ⟨3,false,8,4⟩ .empty) ⟨3,false,8,5⟩ (.node .empty ⟨3,false,8,7⟩ .empty)) ⟨3,false,8,8⟩ (.node (.node .empty ⟨3,false,8,12⟩ .empty) ⟨3,false,8,13⟩ (.node .empty ⟨3,false,8,16⟩ .empty)))
def t65_73 : Tree := (.node (.node (.node (.node .empty ⟨3,true,0,8⟩ .empty) ⟨3,true,1,2⟩ .empty) ⟨3,true,3,1⟩ (.node .empty ⟨3,true,3,4⟩ .empty)) ⟨3,true,3,7⟩ (.node (.node .empty ⟨3,true,3,8⟩ .empty) ⟨3,true,3,10⟩ (.node .empty ⟨3,true,3,18⟩ .empty)))
def t56_73 : Tree := .node t56_64 ⟨3,true,0,7⟩ t65_73
def t37_73 : Tree := .node t37_55 ⟨3,false,8,1⟩ t56_73
def t0_73 : Tree := .node t0_36 ⟨2,true,2,13⟩ t37_73
def t74_83 : Tree := (.node (.node (.node (.node .empty ⟨3,true,6,7⟩ .empty) ⟨3,true,6,8⟩ .empty) ⟨3,true,6,13⟩ (.node .empty ⟨3,true,6,16⟩ .empty)) ⟨3,true,8,1⟩ (.node (.node (.node .empty ⟨3,true,8,4⟩ .empty) ⟨3,true,8,7⟩ .empty) ⟨3,true,8,8⟩ (.node .empty ⟨3,true,8,10⟩ .empty)))
def t84_92 : Tree := (.node (.node (.node (.node .empty ⟨4,true,1,2⟩ .empty) ⟨4,true,1,5⟩ .empty) ⟨4,true,1,12⟩ (.node .empty ⟨4,true,1,13⟩ .empty)) ⟨4,true,1,16⟩ (.node (.node .empty ⟨4,true,2,1⟩ .empty) ⟨4,true,5,0⟩ (.node .empty ⟨4,true,5,2⟩ .empty)))
def t74_92 : Tree := .node t74_83 ⟨3,true,8,18⟩ t84_92
def t93_101 : Tree := (.node (.node (.node (.node .empty ⟨4,true,5,5⟩ .empty) ⟨4,true,5,9⟩ .empty) ⟨4,true,5,12⟩ (.node .empty ⟨4,true,5,13⟩ .empty)) ⟨4,true,5,14⟩ (.node (.node .empty ⟨4,true,5,16⟩ .empty) ⟨4,true,5,17⟩ (.node .empty ⟨4,true,7,1⟩ .empty)))
def t102_110 : Tree := (.node (.node (.node (.node .empty ⟨4,true,7,5⟩ .empty) ⟨4,true,7,7⟩ .empty) ⟨4,true,7,8⟩ (.node .empty ⟨4,true,7,12⟩ .empty)) ⟨4,true,7,13⟩ (.node (.node .empty ⟨4,true,7,16⟩ .empty) ⟨5,false,0,5⟩ (.node .empty ⟨5,false,0,10⟩ .empty)))
def t93_110 : Tree := .node t93_101 ⟨4,true,7,2⟩ t102_110
def t74_110 : Tree := .node t74_92 ⟨4,true,5,3⟩ t93_110
def t111_120 : Tree := (.node (.node (.node (.node .empty ⟨5,false,2,1⟩ .empty) ⟨5,false,2,10⟩ .empty) ⟨5,false,2,11⟩ (.node .empty ⟨5,false,7,1⟩ .empty)) ⟨5,false,7,10⟩ (.node (.node (.node .empty ⟨5,false,7,11⟩ .empty) ⟨5,true,0,4⟩ .empty) ⟨5,true,0,8⟩ (.node .empty ⟨5,true,0,9⟩ .empty)))
def t121_129 : Tree := (.node (.node (.node (.node .empty ⟨5,true,1,5⟩ .empty) ⟨5,true,1,12⟩ .empty) ⟨5,true,1,13⟩ (.node .empty ⟨5,true,2,4⟩ .empty)) ⟨5,true,2,8⟩ (.node (.node .empty ⟨5,true,2,10⟩ .empty) ⟨5,true,2,18⟩ (.node .empty ⟨5,true,3,0⟩ .empty)))
def t111_129 : Tree := .node t111_120 ⟨5,true,1,3⟩ t121_129
def t130_138 : Tree := (.node (.node (.node (.node .empty ⟨5,true,3,9⟩ .empty) ⟨5,true,3,15⟩ .empty) ⟨5,true,6,3⟩ (.node .empty ⟨5,true,6,5⟩ .empty)) ⟨5,true,6,9⟩ (.node (.node .empty ⟨5,true,6,12⟩ .empty) ⟨5,true,6,13⟩ (.node .empty ⟨5,true,6,14⟩ .empty)))
def t139_147 : Tree := (.node (.node (.node (.node .empty ⟨5,true,7,4⟩ .empty) ⟨5,true,7,8⟩ .empty) ⟨5,true,7,10⟩ (.node .empty ⟨5,true,7,18⟩ .empty)) ⟨5,true,8,0⟩ (.node (.node .empty ⟨5,true,8,6⟩ .empty) ⟨5,true,8,9⟩ (.node .empty ⟨5,true,8,15⟩ .empty)))
def t130_147 : Tree := .node t130_138 ⟨5,true,6,17⟩ t139_147
def t111_147 : Tree := .node t111_129 ⟨5,true,3,6⟩ t130_147
def t74_147 : Tree := .node t74_110 ⟨5,false,0,13⟩ t111_147
def t0_147 : Tree := .node t0_73 ⟨3,true,6,2⟩ t74_147
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 6, 0, 5, 0, 0, 0, 0, 0, 7, 8, 6, 0, 5],#[0, 1, 3, 2, 9, 7, 6, 4, 3, 5, 9, 8, 0, 11, 17, 16, 14, 13, 15, 10, 0, 12, 0, 0, 9, 8, 9, 8, 6, 18, 0, 11, 9, 7, 6, 18, 0, 12],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,3),(true,8)],[(true,2),(true,7)],[(true,6)],[(false,7)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1),(false,4)],[(true,3)],[(true,4)],[(false,3),(false,14),(false,17)],[(true,2),(true,16)],[(true,5),(true,12),(true,13)],[(false,2),(false,5),(false,12),(false,13),(false,16)],[(true,9)],[(true,6),(true,15)],[(true,10),(true,18)],[(true,8)],[(false,8)],[(false,9)],[(true,7)],[(false,7)],[(true,14),(true,17)]],
  t0_147⟩
theorem check0_9 : t0_9.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check10_18 : t10_18.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node9 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,1,0⟩ = true := by decide
theorem check0_18 : t0_18.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node9 check0_9 check10_18
theorem check19_27 : t19_27.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check28_36 : t28_36.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node27 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,7,9⟩ = true := by decide
theorem check19_36 : t19_36.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node27 check19_27 check28_36
theorem node18 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,2,2⟩ = true := by decide
theorem check0_36 : t0_36.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node18 check0_18 check19_36
theorem check37_46 : t37_46.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check47_55 : t47_55.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node46 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,4,8⟩ = true := by decide
theorem check37_55 : t37_55.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node46 check37_46 check47_55
theorem check56_64 : t56_64.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check65_73 : t65_73.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node64 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,0,7⟩ = true := by decide
theorem check56_73 : t56_73.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node64 check56_64 check65_73
theorem node55 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,8,1⟩ = true := by decide
theorem check37_73 : t37_73.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node55 check37_55 check56_73
theorem node36 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,2,13⟩ = true := by decide
theorem check0_73 : t0_73.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node36 check0_36 check37_73
theorem check74_83 : t74_83.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check84_92 : t84_92.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node83 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,8,18⟩ = true := by decide
theorem check74_92 : t74_92.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node83 check74_83 check84_92
theorem check93_101 : t93_101.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check102_110 : t102_110.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node101 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,7,2⟩ = true := by decide
theorem check93_110 : t93_110.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node101 check93_101 check102_110
theorem node92 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,5,3⟩ = true := by decide
theorem check74_110 : t74_110.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node92 check74_92 check93_110
theorem check111_120 : t111_120.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check121_129 : t121_129.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node120 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,1,3⟩ = true := by decide
theorem check111_129 : t111_129.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node120 check111_120 check121_129
theorem check130_138 : t130_138.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check139_147 : t139_147.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node138 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,6,17⟩ = true := by decide
theorem check130_147 : t130_147.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node138 check130_138 check139_147
theorem node129 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,3,6⟩ = true := by decide
theorem check111_147 : t111_147.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node129 check111_129 check130_147
theorem node110 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,0,13⟩ = true := by decide
theorem check74_147 : t74_147.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node110 check74_110 check111_147
theorem node73 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,6,2⟩ = true := by decide
theorem check0_147 : t0_147.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node73 check0_73 check74_147
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_147
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M097
