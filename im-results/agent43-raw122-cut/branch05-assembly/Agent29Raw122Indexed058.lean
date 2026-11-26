import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M058
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
def t0_16 : Tree := (.node (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,4⟩ .empty) ⟨0,false,0,10⟩ (.node .empty ⟨1,false,1,0⟩ .empty)) ⟨1,false,1,3⟩ (.node (.node .empty ⟨1,false,1,9⟩ .empty) ⟨1,false,1,13⟩ (.node .empty ⟨1,false,5,7⟩ .empty))) ⟨1,false,7,3⟩ (.node (.node (.node .empty ⟨1,false,7,9⟩ .empty) ⟨1,false,7,13⟩ (.node .empty ⟨1,true,0,5⟩ .empty)) ⟨1,true,0,11⟩ (.node (.node .empty ⟨2,false,2,0⟩ .empty) ⟨2,false,2,1⟩ (.node .empty ⟨2,false,2,6⟩ .empty))))
def t17_32 : Tree := (.node (.node (.node (.node .empty ⟨2,false,8,1⟩ .empty) ⟨2,false,8,6⟩ (.node .empty ⟨2,false,8,12⟩ .empty)) ⟨2,true,2,8⟩ (.node (.node .empty ⟨2,true,6,4⟩ .empty) ⟨2,true,6,10⟩ (.node .empty ⟨2,true,8,8⟩ .empty))) ⟨3,false,2,1⟩ (.node (.node (.node .empty ⟨3,false,2,6⟩ .empty) ⟨3,false,3,0⟩ (.node .empty ⟨3,false,3,11⟩ .empty)) ⟨3,false,8,6⟩ (.node (.node .empty ⟨3,false,9,11⟩ .empty) ⟨3,true,1,2⟩ (.node .empty ⟨3,true,1,14⟩ .empty))))
def t0_32 : Tree := .node t0_16 ⟨2,false,2,12⟩ t17_32
def t33_49 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,true,3,5⟩ .empty) ⟨3,true,3,11⟩ .empty) ⟨3,true,7,14⟩ (.node .empty ⟨3,true,9,0⟩ .empty)) ⟨3,true,9,5⟩ (.node (.node .empty ⟨3,true,9,11⟩ .empty) ⟨4,false,0,6⟩ (.node .empty ⟨4,false,4,0⟩ .empty))) ⟨4,false,4,4⟩ (.node (.node (.node .empty ⟨4,false,4,10⟩ .empty) ⟨4,true,1,9⟩ (.node .empty ⟨4,true,2,1⟩ .empty)) ⟨4,true,2,6⟩ (.node (.node .empty ⟨4,true,3,7⟩ .empty) ⟨4,true,7,9⟩ (.node .empty ⟨4,true,8,6⟩ .empty))))
def t50_65 : Tree := (.node (.node (.node (.node .empty ⟨5,false,0,5⟩ .empty) ⟨5,false,0,11⟩ (.node .empty ⟨5,false,2,8⟩ .empty)) ⟨5,false,4,4⟩ (.node (.node .empty ⟨5,false,4,10⟩ .empty) ⟨5,false,8,8⟩ (.node .empty ⟨5,true,0,4⟩ .empty))) ⟨5,true,0,10⟩ (.node (.node (.node .empty ⟨5,true,1,3⟩ .empty) ⟨5,true,1,13⟩ (.node .empty ⟨5,true,2,12⟩ .empty)) ⟨5,true,5,11⟩ (.node (.node .empty ⟨5,true,6,10⟩ .empty) ⟨5,true,7,13⟩ (.node .empty ⟨5,true,8,12⟩ .empty))))
def t33_65 : Tree := .node t33_49 ⟨4,true,9,7⟩ t50_65
def t0_65 : Tree := .node t0_32 ⟨3,true,3,0⟩ t33_65
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 5, 0, 4, 1, 0, 0, 6, 0, 7, 0, 8, 9, 5, 0, 4],#[0, 1, 3, 2, 0, 0, 4, 0, 5, 7, 0, 6, 13, 14, 8, 0, 0, 9, 10, 0, 11, 7, 12, 6, 13, 0, 10, 0, 0, 0],
  #[[(false,0)],[(false,4),(true,0)],[(true,1)],[(false,2)],[(true,3),(true,9)],[(true,2),(true,8)],[(true,5)],[(true,6)],[(true,7)],[(false,8)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(false,4)],[(true,5),(true,11)],[(true,4),(true,10)],[(false,7)],[(true,8)],[(false,9),(false,13)],[(false,10)],[(false,11)],[(false,6),(false,12)],[(true,6)]],
  t0_65⟩
theorem check0_16 : t0_16.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check17_32 : t17_32.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node16 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,2,12⟩ = true := by decide
theorem check0_32 : t0_32.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node16 check0_16 check17_32
theorem check33_49 : t33_49.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check50_65 : t50_65.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node49 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,9,7⟩ = true := by decide
theorem check33_65 : t33_65.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node49 check33_49 check50_65
theorem node32 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,3,0⟩ = true := by decide
theorem check0_65 : t0_65.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node32 check0_32 check33_65
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_65
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M058
