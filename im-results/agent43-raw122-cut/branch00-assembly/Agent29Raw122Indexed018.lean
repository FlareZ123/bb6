import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M018
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_16 : Tree := (.node (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,4⟩ .empty) ⟨0,false,2,9⟩ (.node .empty ⟨0,false,8,0⟩ .empty)) ⟨0,false,8,4⟩ (.node (.node .empty ⟨0,true,0,4⟩ .empty) ⟨0,true,2,10⟩ (.node .empty ⟨0,true,8,4⟩ .empty))) ⟨1,false,1,0⟩ (.node (.node (.node .empty ⟨1,false,1,3⟩ .empty) ⟨1,false,7,8⟩ (.node .empty ⟨2,false,2,0⟩ .empty)) ⟨2,false,2,1⟩ (.node (.node .empty ⟨2,false,2,6⟩ .empty) ⟨2,false,2,10⟩ (.node .empty ⟨2,false,5,0⟩ .empty))))
def t17_32 : Tree := (.node (.node (.node (.node .empty ⟨2,false,8,2⟩ .empty) ⟨2,false,8,7⟩ (.node .empty ⟨2,false,8,13⟩ .empty)) ⟨2,true,0,5⟩ (.node (.node .empty ⟨3,false,2,1⟩ .empty) ⟨3,false,2,6⟩ (.node .empty ⟨3,false,3,0⟩ .empty))) ⟨3,false,3,5⟩ (.node (.node (.node .empty ⟨3,false,4,2⟩ .empty) ⟨3,false,4,7⟩ (.node .empty ⟨3,false,4,13⟩ .empty)) ⟨3,false,5,1⟩ (.node (.node .empty ⟨3,false,5,2⟩ .empty) ⟨3,false,5,11⟩ (.node .empty ⟨3,false,5,12⟩ .empty))))
def t0_32 : Tree := .node t0_16 ⟨2,false,5,3⟩ t17_32
def t33_48 : Tree := (.node (.node (.node (.node .empty ⟨3,false,6,1⟩ .empty) ⟨3,false,6,6⟩ (.node .empty ⟨3,false,6,10⟩ .empty)) ⟨3,true,1,2⟩ (.node (.node .empty ⟨3,true,1,11⟩ .empty) ⟨3,true,3,0⟩ (.node .empty ⟨3,true,3,5⟩ .empty))) ⟨3,true,3,7⟩ (.node (.node (.node .empty ⟨3,true,3,14⟩ .empty) ⟨3,true,9,1⟩ (.node .empty ⟨3,true,9,2⟩ .empty)) ⟨3,true,9,11⟩ (.node (.node .empty ⟨3,true,9,12⟩ .empty) ⟨4,false,0,6⟩ (.node .empty ⟨4,false,4,0⟩ .empty))))
def t49_64 : Tree := (.node (.node (.node (.node .empty ⟨4,true,2,1⟩ .empty) ⟨4,true,2,6⟩ (.node .empty ⟨4,true,4,2⟩ .empty)) ⟨4,true,4,7⟩ (.node (.node .empty ⟨4,true,4,13⟩ .empty) ⟨4,true,10,0⟩ (.node .empty ⟨4,true,10,1⟩ .empty))) ⟨4,true,10,6⟩ (.node (.node (.node .empty ⟨4,true,10,10⟩ .empty) ⟨5,false,0,5⟩ (.node .empty ⟨5,true,1,3⟩ .empty)) ⟨5,true,3,8⟩ (.node (.node .empty ⟨5,true,7,5⟩ .empty) ⟨5,true,9,0⟩ (.node .empty ⟨5,true,9,3⟩ .empty))))
def t33_64 : Tree := .node t33_48 ⟨4,false,4,4⟩ t49_64
def t0_64 : Tree := .node t0_32 ⟨3,false,6,0⟩ t33_64
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 7, 0, 4, 5, 0, 6, 0, 0, 0, 0, 8, 9, 1, 0, 10, 0, 0],#[0, 1, 3, 2, 8, 7, 4, 0, 5, 0, 10, 6, 3, 11, 8, 14, 9, 0, 0, 0, 3, 12, 0, 13, 0, 13, 8, 14, 0, 0],
  #[[(false,0)],[(true,0),(true,8)],[(true,1)],[(false,2)],[(true,3)],[(false,4)],[(false,5)],[(true,2)],[(true,7)],[(false,8)],[(true,9)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1),(false,6),(false,10)],[(false,3)],[(false,4)],[(true,5)],[(true,2)],[(false,2),(false,7),(false,13)],[(false,8)],[(false,5)],[(true,6)],[(true,10)],[(true,11),(true,12)],[(true,7),(true,13)]],
  t0_64⟩
theorem check0_16 : t0_16.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check17_32 : t17_32.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node16 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,5,3⟩ = true := by decide
theorem check0_32 : t0_32.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node16 check0_16 check17_32
theorem check33_48 : t33_48.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check49_64 : t49_64.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node48 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,4,4⟩ = true := by decide
theorem check33_64 : t33_64.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node48 check33_48 check49_64
theorem node32 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,6,0⟩ = true := by decide
theorem check0_64 : t0_64.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node32 check0_32 check33_64
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_64
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M018
