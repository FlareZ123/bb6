import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M095
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def t0_16 : Tree := (.node (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,1,6⟩ .empty) ⟨0,true,1,4⟩ (.node .empty ⟨0,true,1,13⟩ .empty)) ⟨0,true,1,22⟩ (.node (.node .empty ⟨0,true,1,23⟩ .empty) ⟨0,true,9,3⟩ (.node .empty ⟨0,true,10,8⟩ .empty))) ⟨0,true,14,16⟩ (.node (.node (.node .empty ⟨1,false,1,0⟩ .empty) ⟨1,false,2,4⟩ (.node .empty ⟨1,false,2,13⟩ .empty)) ⟨1,false,2,22⟩ (.node (.node .empty ⟨1,false,2,23⟩ .empty) ⟨1,false,4,12⟩ (.node .empty ⟨1,false,4,21⟩ .empty))))
def t17_32 : Tree := (.node (.node (.node (.node .empty ⟨1,false,4,23⟩ .empty) ⟨1,false,5,1⟩ (.node .empty ⟨1,false,7,0⟩ .empty)) ⟨1,false,10,20⟩ (.node (.node .empty ⟨1,false,10,21⟩ .empty) ⟨1,false,10,22⟩ (.node .empty ⟨1,false,10,23⟩ .empty))) ⟨1,false,11,10⟩ (.node (.node (.node .empty ⟨1,false,14,20⟩ .empty) ⟨1,false,14,21⟩ (.node .empty ⟨1,false,14,22⟩ .empty)) ⟨1,false,14,23⟩ (.node (.node .empty ⟨1,false,15,18⟩ .empty) ⟨1,true,5,11⟩ (.node .empty ⟨1,true,5,20⟩ .empty))))
def t0_32 : Tree := .node t0_16 ⟨1,false,4,22⟩ t17_32
def t33_48 : Tree := (.node (.node (.node (.node .empty ⟨1,true,5,22⟩ .empty) ⟨1,true,5,23⟩ (.node .empty ⟨1,true,11,19⟩ .empty)) ⟨1,true,11,20⟩ (.node (.node .empty ⟨1,true,11,21⟩ .empty) ⟨1,true,11,22⟩ (.node .empty ⟨1,true,11,23⟩ .empty))) ⟨1,true,15,19⟩ (.node (.node (.node .empty ⟨1,true,15,20⟩ .empty) ⟨1,true,15,21⟩ (.node .empty ⟨1,true,15,22⟩ .empty)) ⟨1,true,15,23⟩ (.node (.node .empty ⟨2,false,2,0⟩ .empty) ⟨2,false,8,0⟩ (.node .empty ⟨2,false,12,8⟩ .empty))))
def t49_64 : Tree := (.node (.node (.node (.node .empty ⟨2,true,4,3⟩ .empty) ⟨2,true,4,12⟩ (.node .empty ⟨2,true,4,21⟩ .empty)) ⟨2,true,4,22⟩ (.node (.node .empty ⟨2,true,4,23⟩ .empty) ⟨2,true,6,0⟩ (.node .empty ⟨2,true,10,11⟩ .empty))) ⟨2,true,10,20⟩ (.node (.node (.node .empty ⟨2,true,10,21⟩ .empty) ⟨2,true,10,22⟩ (.node .empty ⟨2,true,10,23⟩ .empty)) ⟨2,true,14,19⟩ (.node (.node .empty ⟨2,true,14,20⟩ .empty) ⟨2,true,14,21⟩ (.node .empty ⟨2,true,14,22⟩ .empty))))
def t33_64 : Tree := .node t33_48 ⟨2,false,16,16⟩ t49_64
def t0_64 : Tree := .node t0_32 ⟨1,true,5,21⟩ t33_64
def t65_81 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,false,2,1⟩ .empty) ⟨3,false,3,0⟩ .empty) ⟨3,false,8,1⟩ (.node .empty ⟨3,false,12,14⟩ .empty)) ⟨3,false,12,15⟩ (.node (.node .empty ⟨3,false,13,7⟩ .empty) ⟨3,false,13,14⟩ (.node .empty ⟨3,false,13,15⟩ .empty))) ⟨3,false,16,14⟩ (.node (.node (.node .empty ⟨3,false,16,15⟩ .empty) ⟨3,true,1,2⟩ (.node .empty ⟨3,true,7,2⟩ .empty)) ⟨3,true,11,15⟩ (.node (.node .empty ⟨3,true,15,15⟩ .empty) ⟨4,true,0,6⟩ (.node .empty ⟨4,true,2,1⟩ .empty))))
def t82_97 : Tree := (.node (.node (.node (.node .empty ⟨4,true,6,7⟩ .empty) ⟨4,true,8,1⟩ (.node .empty ⟨4,true,10,18⟩ .empty)) ⟨4,true,12,14⟩ (.node (.node .empty ⟨4,true,12,15⟩ .empty) ⟨4,true,14,18⟩ (.node .empty ⟨4,true,16,14⟩ .empty))) ⟨4,true,16,15⟩ (.node (.node (.node .empty ⟨5,false,0,5⟩ .empty) ⟨5,false,0,23⟩ (.node .empty ⟨5,false,4,9⟩ .empty)) ⟨5,false,6,4⟩ (.node (.node .empty ⟨5,false,10,17⟩ .empty) ⟨5,false,14,17⟩ (.node .empty ⟨5,true,0,4⟩ .empty))))
def t65_97 : Tree := .node t65_81 ⟨4,true,4,10⟩ t82_97
def t98_113 : Tree := (.node (.node (.node (.node .empty ⟨5,true,0,22⟩ .empty) ⟨5,true,0,23⟩ (.node .empty ⟨5,true,1,3⟩ .empty)) ⟨5,true,1,12⟩ (.node (.node .empty ⟨5,true,1,21⟩ .empty) ⟨5,true,1,22⟩ (.node .empty ⟨5,true,1,23⟩ .empty))) ⟨5,true,2,11⟩ (.node (.node (.node .empty ⟨5,true,2,20⟩ .empty) ⟨5,true,2,21⟩ (.node .empty ⟨5,true,2,22⟩ .empty)) ⟨5,true,2,23⟩ (.node (.node .empty ⟨5,true,4,19⟩ .empty) ⟨5,true,4,20⟩ (.node .empty ⟨5,true,4,21⟩ .empty))))
def t114_129 : Tree := (.node (.node (.node (.node .empty ⟨5,true,4,23⟩ .empty) ⟨5,true,5,8⟩ (.node .empty ⟨5,true,7,3⟩ .empty)) ⟨5,true,10,19⟩ (.node (.node .empty ⟨5,true,10,20⟩ .empty) ⟨5,true,10,21⟩ (.node .empty ⟨5,true,10,22⟩ .empty))) ⟨5,true,10,23⟩ (.node (.node (.node .empty ⟨5,true,11,16⟩ .empty) ⟨5,true,14,19⟩ (.node .empty ⟨5,true,14,20⟩ .empty)) ⟨5,true,14,21⟩ (.node (.node .empty ⟨5,true,14,22⟩ .empty) ⟨5,true,14,23⟩ (.node .empty ⟨5,true,15,16⟩ .empty))))
def t98_129 : Tree := .node t98_113 ⟨5,true,4,22⟩ t114_129
def t65_129 : Tree := .node t65_97 ⟨5,true,0,13⟩ t98_129
def t0_129 : Tree := .node t0_64 ⟨2,true,14,23⟩ t65_129
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 4, 0, 0, 5, 10, 0, 6, 7, 9, 0, 8, 3, 0, 0, 0, 11, 14, 0, 12, 13, 0, 0, 0, 15, 14, 0, 16, 13, 0],#[0, 1, 3, 2, 0, 0, 7, 4, 6, 5, 0, 0, 5, 0, 8, 14, 10, 9, 0, 0, 11, 0, 0, 12, 0, 13, 6, 5, 16, 15, 16, 15, 18, 17, 0, 0, 19, 0, 0, 20, 0, 21, 0, 22, 6, 23, 6, 23],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2),(false,8)],[(true,2)],[(false,4)],[(true,5)],[(false,6)],[(true,7)],[(true,6)],[(true,4)],[(false,10)],[(true,11)],[(false,12),(false,16)],[(true,10),(true,14)],[(false,14)],[(true,15)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3)],[(false,6),(true,4),(true,13)],[(false,4),(false,13),(false,22),(false,23)],[(false,3)],[(false,7)],[(true,8)],[(false,8)],[(false,10)],[(true,11)],[(true,12)],[(true,7)],[(true,14),(true,15)],[(false,14),(false,15)],[(true,16)],[(false,16)],[(false,18)],[(true,19)],[(true,20)],[(true,21)],[(true,22),(true,23)]],
  t0_129⟩
theorem check0_16 : t0_16.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check17_32 : t17_32.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node16 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,4,22⟩ = true := by decide
theorem check0_32 : t0_32.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node16 check0_16 check17_32
theorem check33_48 : t33_48.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check49_64 : t49_64.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node48 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,16,16⟩ = true := by decide
theorem check33_64 : t33_64.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node48 check33_48 check49_64
theorem node32 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,5,21⟩ = true := by decide
theorem check0_64 : t0_64.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node32 check0_32 check33_64
theorem check65_81 : t65_81.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check82_97 : t82_97.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node81 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,4,10⟩ = true := by decide
theorem check65_97 : t65_97.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node81 check65_81 check82_97
theorem check98_113 : t98_113.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check114_129 : t114_129.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node113 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,4,22⟩ = true := by decide
theorem check98_129 : t98_129.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node113 check98_113 check114_129
theorem node97 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,0,13⟩ = true := by decide
theorem check65_129 : t65_129.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node97 check65_97 check98_129
theorem node64 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,14,23⟩ = true := by decide
theorem check0_129 : t0_129.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node64 check0_64 check65_129
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_129
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M095
