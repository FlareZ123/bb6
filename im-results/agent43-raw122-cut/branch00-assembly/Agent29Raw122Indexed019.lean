import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M019
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_10 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,6⟩ .empty) ⟨0,false,0,16⟩ (.node (.node .empty ⟨0,false,4,4⟩ .empty) ⟨0,false,4,14⟩ .empty)) ⟨0,false,4,19⟩ (.node (.node (.node .empty ⟨0,false,4,21⟩ .empty) ⟨0,false,6,9⟩ .empty) ⟨0,false,12,0⟩ (.node .empty ⟨0,false,12,4⟩ .empty)))
def t11_20 : Tree := (.node (.node (.node (.node .empty ⟨0,false,12,19⟩ .empty) ⟨0,false,16,9⟩ .empty) ⟨0,false,18,6⟩ (.node .empty ⟨0,false,18,12⟩ .empty)) ⟨0,false,18,16⟩ (.node (.node (.node .empty ⟨0,true,0,4⟩ .empty) ⟨0,true,0,14⟩ .empty) ⟨0,true,0,21⟩ (.node .empty ⟨0,true,4,6⟩ .empty)))
def t0_20 : Tree := .node t0_10 ⟨0,false,12,12⟩ t11_20
def t21_31 : Tree := (.node (.node (.node (.node .empty ⟨0,true,4,16⟩ .empty) ⟨0,true,6,10⟩ .empty) ⟨0,true,12,4⟩ (.node (.node .empty ⟨0,true,12,12⟩ .empty) ⟨0,true,12,19⟩ .empty)) ⟨0,true,16,10⟩ (.node (.node (.node .empty ⟨0,true,18,14⟩ .empty) ⟨0,true,18,19⟩ .empty) ⟨0,true,18,21⟩ (.node .empty ⟨1,false,1,0⟩ .empty)))
def t32_41 : Tree := (.node (.node (.node (.node .empty ⟨1,false,5,15⟩ .empty) ⟨1,false,5,18⟩ .empty) ⟨1,false,11,8⟩ (.node .empty ⟨1,false,15,0⟩ .empty)) ⟨1,false,15,3⟩ (.node (.node (.node .empty ⟨1,false,15,11⟩ .empty) ⟨1,false,15,15⟩ .empty) ⟨1,false,15,18⟩ (.node .empty ⟨1,false,19,11⟩ .empty)))
def t21_41 : Tree := .node t21_31 ⟨1,false,5,3⟩ t32_41
def t0_41 : Tree := .node t0_20 ⟨0,true,4,12⟩ t21_41
def t42_52 : Tree := (.node (.node (.node (.node .empty ⟨1,true,1,15⟩ .empty) ⟨1,true,1,20⟩ .empty) ⟨1,true,1,22⟩ (.node (.node .empty ⟨1,true,5,13⟩ .empty) ⟨1,true,5,18⟩ .empty)) ⟨1,true,5,25⟩ (.node (.node (.node .empty ⟨1,true,19,5⟩ .empty) ⟨1,true,19,15⟩ .empty) ⟨1,true,19,20⟩ (.node .empty ⟨1,true,19,22⟩ .empty)))
def t53_62 : Tree := (.node (.node (.node (.node .empty ⟨2,false,6,1⟩ .empty) ⟨2,false,6,6⟩ .empty) ⟨2,false,6,14⟩ (.node .empty ⟨2,false,9,0⟩ .empty)) ⟨2,false,9,3⟩ (.node (.node (.node .empty ⟨2,false,9,11⟩ .empty) ⟨2,false,9,15⟩ .empty) ⟨2,false,9,18⟩ (.node .empty ⟨2,false,12,2⟩ .empty)))
def t42_62 : Tree := .node t42_52 ⟨2,false,2,0⟩ t53_62
def t63_72 : Tree := (.node (.node (.node (.node .empty ⟨2,false,12,23⟩ .empty) ⟨2,false,16,0⟩ .empty) ⟨2,false,16,1⟩ (.node .empty ⟨2,false,16,6⟩ .empty)) ⟨2,false,16,10⟩ (.node (.node (.node .empty ⟨2,false,16,14⟩ .empty) ⟨2,false,20,10⟩ .empty) ⟨3,false,2,1⟩ (.node .empty ⟨3,false,3,0⟩ .empty)))
def t73_82 : Tree := (.node (.node (.node (.node .empty ⟨3,false,8,7⟩ .empty) ⟨3,false,8,23⟩ .empty) ⟨3,false,9,1⟩ (.node .empty ⟨3,false,9,2⟩ .empty)) ⟨3,false,9,17⟩ (.node (.node (.node .empty ⟨3,false,9,26⟩ .empty) ⟨3,false,10,0⟩ .empty) ⟨3,false,10,1⟩ (.node .empty ⟨3,false,10,6⟩ .empty)))
def t63_82 : Tree := .node t63_72 ⟨3,false,8,2⟩ t73_82
def t42_82 : Tree := .node t42_62 ⟨2,false,12,7⟩ t63_82
def t0_82 : Tree := .node t0_41 ⟨1,true,1,5⟩ t42_82
def t83_93 : Tree := (.node (.node (.node (.node .empty ⟨3,false,10,14⟩ .empty) ⟨3,false,16,1⟩ .empty) ⟨3,false,16,6⟩ (.node (.node .empty ⟨3,false,16,14⟩ .empty) ⟨3,false,17,0⟩ .empty)) ⟨3,false,17,5⟩ (.node (.node (.node .empty ⟨3,false,17,13⟩ .empty) ⟨3,false,17,20⟩ .empty) ⟨3,false,20,6⟩ (.node .empty ⟨3,false,20,14⟩ .empty)))
def t94_103 : Tree := (.node (.node (.node (.node .empty ⟨3,false,21,13⟩ .empty) ⟨3,false,21,20⟩ .empty) ⟨3,true,1,2⟩ (.node .empty ⟨3,true,7,0⟩ .empty)) ⟨3,true,7,5⟩ (.node (.node (.node .empty ⟨3,true,7,7⟩ .empty) ⟨3,true,7,13⟩ .empty) ⟨3,true,7,20⟩ (.node .empty ⟨3,true,7,24⟩ .empty)))
def t83_103 : Tree := .node t83_93 ⟨3,false,21,5⟩ t94_103
def t104_113 : Tree := (.node (.node (.node (.node .empty ⟨3,true,13,2⟩ .empty) ⟨3,true,13,17⟩ .empty) ⟨3,true,13,26⟩ (.node .empty ⟨3,true,15,2⟩ .empty)) ⟨3,true,15,17⟩ (.node (.node (.node .empty ⟨3,true,17,0⟩ .empty) ⟨3,true,17,5⟩ .empty) ⟨3,true,17,7⟩ (.node .empty ⟨3,true,17,13⟩ .empty)))
def t114_123 : Tree := (.node (.node (.node (.node .empty ⟨3,true,17,24⟩ .empty) ⟨3,true,19,17⟩ .empty) ⟨4,false,8,0⟩ (.node .empty ⟨4,false,8,4⟩ .empty)) ⟨4,false,8,12⟩ (.node (.node (.node .empty ⟨4,false,8,19⟩ .empty) ⟨4,true,2,1⟩ .empty) ⟨4,true,8,2⟩ (.node .empty ⟨4,true,8,7⟩ .empty)))
def t104_123 : Tree := .node t104_113 ⟨3,true,17,20⟩ t114_123
def t83_123 : Tree := .node t83_103 ⟨3,true,13,1⟩ t104_123
def t124_134 : Tree := (.node (.node (.node (.node .empty ⟨4,true,14,0⟩ .empty) ⟨4,true,14,1⟩ .empty) ⟨4,true,14,6⟩ (.node (.node .empty ⟨4,true,14,10⟩ .empty) ⟨4,true,14,14⟩ .empty)) ⟨4,true,16,1⟩ (.node (.node (.node .empty ⟨4,true,16,6⟩ .empty) ⟨4,true,16,14⟩ .empty) ⟨4,true,20,6⟩ (.node .empty ⟨4,true,20,14⟩ .empty)))
def t135_144 : Tree := (.node (.node (.node (.node .empty ⟨5,false,0,15⟩ .empty) ⟨5,false,0,22⟩ .empty) ⟨5,false,1,13⟩ (.node .empty ⟨5,false,1,18⟩ .empty)) ⟨5,false,1,25⟩ (.node (.node (.node .empty ⟨5,false,5,15⟩ .empty) ⟨5,false,5,20⟩ .empty) ⟨5,false,5,22⟩ (.node .empty ⟨5,false,19,13⟩ .empty)))
def t124_144 : Tree := .node t124_134 ⟨5,false,0,5⟩ t135_144
def t145_154 : Tree := (.node (.node (.node (.node .empty ⟨5,false,19,25⟩ .empty) ⟨5,true,1,3⟩ .empty) ⟨5,true,5,11⟩ (.node .empty ⟨5,true,7,8⟩ .empty)) ⟨5,true,11,5⟩ (.node (.node (.node .empty ⟨5,true,11,13⟩ .empty) ⟨5,true,11,20⟩ .empty) ⟨5,true,13,0⟩ (.node .empty ⟨5,true,13,3⟩ .empty)))
def t155_164 : Tree := (.node (.node (.node (.node .empty ⟨5,true,13,15⟩ .empty) ⟨5,true,13,18⟩ .empty) ⟨5,true,15,3⟩ (.node .empty ⟨5,true,15,11⟩ .empty)) ⟨5,true,15,15⟩ (.node (.node (.node .empty ⟨5,true,15,18⟩ .empty) ⟨5,true,17,8⟩ .empty) ⟨5,true,19,15⟩ (.node .empty ⟨5,true,19,18⟩ .empty)))
def t145_164 : Tree := .node t145_154 ⟨5,true,13,11⟩ t155_164
def t124_164 : Tree := .node t124_144 ⟨5,false,19,18⟩ t145_164
def t83_164 : Tree := .node t83_123 ⟨4,true,8,23⟩ t124_164
def t0_164 : Tree := .node t0_82 ⟨3,false,10,10⟩ t83_164
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 0, 0, 0, 0, 5, 18, 6, 7, 11, 0, 8, 9, 0, 10, 0, 0, 0, 0, 12, 13, 15, 0, 14, 0, 0, 0, 16, 17, 11, 0, 8, 0, 19, 4, 20, 21, 0, 0, 0],#[0, 1, 3, 2, 8, 7, 4, 0, 5, 0, 10, 6, 18, 17, 8, 24, 9, 0, 0, 0, 11, 26, 12, 0, 13, 0, 10, 14, 15, 17, 19, 16, 25, 0, 0, 23, 19, 21, 20, 0, 10, 6, 22, 0, 0, 16, 8, 24, 0, 0, 0, 21, 0, 23],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1),(false,19)],[(true,4)],[(true,5)],[(false,6)],[(true,7),(true,17)],[(false,8)],[(false,9)],[(true,6),(true,16)],[(true,11)],[(false,12)],[(true,13)],[(true,12)],[(true,15)],[(false,16)],[(false,5)],[(true,18)],[(true,19)],[(false,20)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(false,4)],[(true,5),(true,20)],[(true,2)],[(false,2),(false,7),(false,23)],[(false,8)],[(false,5),(false,13),(false,20)],[(false,10)],[(false,11)],[(false,12)],[(true,13)],[(false,14)],[(true,15),(true,22)],[(true,6),(true,14)],[(false,6)],[(false,15),(false,18)],[(false,19)],[(true,18),(true,25)],[(false,21)],[(true,17),(true,26)],[(true,7),(true,23)],[(false,16)],[(true,10)]],
  t0_164⟩
theorem check0_10 : t0_10.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check11_20 : t11_20.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node10 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,12,12⟩ = true := by decide
theorem check0_20 : t0_20.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node10 check0_10 check11_20
theorem check21_31 : t21_31.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check32_41 : t32_41.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node31 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,5,3⟩ = true := by decide
theorem check21_41 : t21_41.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node31 check21_31 check32_41
theorem node20 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,4,12⟩ = true := by decide
theorem check0_41 : t0_41.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node20 check0_20 check21_41
theorem check42_52 : t42_52.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check53_62 : t53_62.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node52 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,2,0⟩ = true := by decide
theorem check42_62 : t42_62.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node52 check42_52 check53_62
theorem check63_72 : t63_72.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check73_82 : t73_82.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node72 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,8,2⟩ = true := by decide
theorem check63_82 : t63_82.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node72 check63_72 check73_82
theorem node62 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,12,7⟩ = true := by decide
theorem check42_82 : t42_82.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node62 check42_62 check63_82
theorem node41 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,1,5⟩ = true := by decide
theorem check0_82 : t0_82.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node41 check0_41 check42_82
theorem check83_93 : t83_93.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check94_103 : t94_103.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node93 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,21,5⟩ = true := by decide
theorem check83_103 : t83_103.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node93 check83_93 check94_103
theorem check104_113 : t104_113.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check114_123 : t114_123.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node113 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,17,20⟩ = true := by decide
theorem check104_123 : t104_123.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node113 check104_113 check114_123
theorem node103 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,13,1⟩ = true := by decide
theorem check83_123 : t83_123.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node103 check83_103 check104_123
theorem check124_134 : t124_134.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check135_144 : t135_144.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node134 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,0,5⟩ = true := by decide
theorem check124_144 : t124_144.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node134 check124_134 check135_144
theorem check145_154 : t145_154.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check155_164 : t155_164.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node154 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,13,11⟩ = true := by decide
theorem check145_164 : t145_164.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node154 check145_154 check155_164
theorem node144 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,19,18⟩ = true := by decide
theorem check124_164 : t124_164.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node144 check124_144 check145_164
theorem node123 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,8,23⟩ = true := by decide
theorem check83_164 : t83_164.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node123 check83_123 check124_164
theorem node82 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,10,10⟩ = true := by decide
theorem check0_164 : t0_164.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node82 check0_82 check83_164
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_164
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M019
