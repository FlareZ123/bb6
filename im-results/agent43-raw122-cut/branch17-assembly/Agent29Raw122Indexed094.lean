import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M094
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def t0_10 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,1,6⟩ .empty) ⟨0,true,1,4⟩ (.node (.node .empty ⟨0,true,1,15⟩ .empty) ⟨0,true,11,3⟩ .empty)) ⟨0,true,11,12⟩ (.node (.node (.node .empty ⟨0,true,12,9⟩ .empty) ⟨0,true,15,9⟩ .empty) ⟨1,false,1,0⟩ (.node .empty ⟨1,false,2,4⟩ .empty)))
def t11_20 : Tree := (.node (.node (.node (.node .empty ⟨1,false,8,0⟩ .empty) ⟨1,false,8,3⟩ .empty) ⟨1,false,8,12⟩ (.node .empty ⟨2,false,2,0⟩ .empty)) ⟨2,false,5,1⟩ (.node (.node (.node .empty ⟨2,false,5,10⟩ .empty) ⟨2,false,9,0⟩ .empty) ⟨2,false,9,1⟩ (.node .empty ⟨2,false,9,10⟩ .empty)))
def t0_20 : Tree := .node t0_10 ⟨1,false,2,15⟩ t11_20
def t21_30 : Tree := (.node (.node (.node (.node .empty ⟨2,false,13,11⟩ .empty) ⟨2,true,4,3⟩ .empty) ⟨2,true,4,14⟩ (.node .empty ⟨2,true,5,13⟩ .empty)) ⟨2,true,5,17⟩ (.node (.node (.node .empty ⟨2,true,12,5⟩ .empty) ⟨2,true,12,12⟩ .empty) ⟨2,true,13,4⟩ (.node .empty ⟨2,true,13,15⟩ .empty)))
def t31_40 : Tree := (.node (.node (.node (.node .empty ⟨3,false,3,0⟩ .empty) ⟨3,false,9,1⟩ .empty) ⟨3,false,9,10⟩ (.node .empty ⟨3,false,10,0⟩ .empty)) ⟨3,false,10,9⟩ (.node (.node (.node .empty ⟨3,false,13,10⟩ .empty) ⟨3,false,14,9⟩ .empty) ⟨3,true,1,2⟩ (.node .empty ⟨3,true,6,0⟩ .empty)))
def t21_40 : Tree := .node t21_30 ⟨3,false,2,1⟩ t31_40
def t0_40 : Tree := .node t0_20 ⟨2,false,9,11⟩ t21_40
def t41_50 : Tree := (.node (.node (.node (.node .empty ⟨3,true,8,2⟩ .empty) ⟨3,true,8,16⟩ .empty) ⟨3,true,10,0⟩ (.node .empty ⟨3,true,10,9⟩ .empty)) ⟨3,true,12,16⟩ (.node (.node (.node .empty ⟨4,false,7,0⟩ .empty) ⟨4,false,7,8⟩ .empty) ⟨4,true,0,6⟩ (.node .empty ⟨4,true,2,1⟩ .empty)))
def t51_60 : Tree := (.node (.node (.node (.node .empty ⟨4,true,7,8⟩ .empty) ⟨4,true,9,1⟩ .empty) ⟨4,true,9,10⟩ (.node .empty ⟨4,true,9,11⟩ .empty)) ⟨4,true,13,10⟩ (.node (.node (.node .empty ⟨5,false,0,5⟩ .empty) ⟨5,false,0,7⟩ .empty) ⟨5,false,5,10⟩ (.node .empty ⟨5,false,7,4⟩ .empty)))
def t41_60 : Tree := .node t41_50 ⟨4,true,5,11⟩ t51_60
def t61_70 : Tree := (.node (.node (.node (.node .empty ⟨5,false,9,10⟩ .empty) ⟨5,true,0,4⟩ .empty) ⟨5,true,0,15⟩ (.node .empty ⟨5,true,1,3⟩ .empty)) ⟨5,true,1,14⟩ (.node (.node (.node .empty ⟨5,true,2,13⟩ .empty) ⟨5,true,2,17⟩ .empty) ⟨5,true,4,5⟩ (.node .empty ⟨5,true,4,12⟩ .empty)))
def t71_80 : Tree := (.node (.node (.node (.node .empty ⟨5,true,5,15⟩ .empty) ⟨5,true,6,9⟩ .empty) ⟨5,true,8,3⟩ (.node .empty ⟨5,true,8,12⟩ .empty)) ⟨5,true,10,9⟩ (.node (.node (.node .empty ⟨5,true,12,3⟩ .empty) ⟨5,true,12,14⟩ .empty) ⟨5,true,13,13⟩ (.node .empty ⟨5,true,13,17⟩ .empty)))
def t61_80 : Tree := .node t61_70 ⟨5,true,5,4⟩ t71_80
def t41_80 : Tree := .node t41_60 ⟨5,false,7,13⟩ t61_80
def t0_80 : Tree := .node t0_40 ⟨3,true,6,9⟩ t41_80
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 4, 0, 0, 0, 5, 6, 12, 0, 7, 8, 11, 0, 9, 10, 15, 0, 7, 0, 0, 0, 13, 14, 4, 0, 0, 0, 0],#[0, 1, 3, 2, 0, 0, 8, 4, 6, 5, 0, 17, 7, 0, 0, 0, 9, 0, 11, 10, 3, 16, 12, 0, 8, 13, 0, 14, 0, 15, 6, 5, 0, 0, 0, 14],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(true,2),(true,13)],[(true,4)],[(false,5)],[(true,6),(true,10)],[(false,7)],[(true,8)],[(false,9)],[(true,7)],[(true,5)],[(true,12)],[(false,13)],[(true,9)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1),(false,10)],[(true,3)],[(true,4),(true,15)],[(false,4),(false,15)],[(false,6)],[(false,3),(false,12)],[(false,8)],[(true,9)],[(false,9)],[(false,11)],[(true,12)],[(true,13),(true,17)],[(true,14)],[(true,10)],[(true,5)]],
  t0_80⟩
theorem check0_10 : t0_10.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check11_20 : t11_20.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node10 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,2,15⟩ = true := by decide
theorem check0_20 : t0_20.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node10 check0_10 check11_20
theorem check21_30 : t21_30.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check31_40 : t31_40.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node30 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,2,1⟩ = true := by decide
theorem check21_40 : t21_40.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node30 check21_30 check31_40
theorem node20 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,9,11⟩ = true := by decide
theorem check0_40 : t0_40.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node20 check0_20 check21_40
theorem check41_50 : t41_50.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check51_60 : t51_60.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node50 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,5,11⟩ = true := by decide
theorem check41_60 : t41_60.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node50 check41_50 check51_60
theorem check61_70 : t61_70.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check71_80 : t71_80.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node70 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,5,4⟩ = true := by decide
theorem check61_80 : t61_80.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node70 check61_70 check71_80
theorem node60 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,7,13⟩ = true := by decide
theorem check41_80 : t41_80.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node60 check41_60 check61_80
theorem node40 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,6,9⟩ = true := by decide
theorem check0_80 : t0_80.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node40 check0_40 check41_80
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_80
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M094
