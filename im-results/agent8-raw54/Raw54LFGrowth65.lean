import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFGrowth65
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def L (n : Nat) : List Bool := [true,true,false,true,false] ++ rep [false] n ++ [true,true]
def cfg (n : Nat) : Z0 := ⟨5,true::(rep [false] n ++ [true,true]),[true,false,false] ++ rep [true] (n+3)⟩

theorem epoch (n : Nat) : ∃ t,0<t ∧ run0 table t (cfg n) = some (cfg (n+1)) := by
  have a : run0 table 9 (cfg n) = some ⟨2,true::L n,rep [true] (n+1)⟩ := by rfl
  have b := sweepR table 2 [true] [] [true] [false] 1 (by intro L R; rfl) (n+1) (L n) []
  have c : run0 table 2 ⟨2,[true] ++ rep [false] (n+1) ++ L n,[]⟩ = some ⟨3,[false,false,false] ++ rep [false] (n+1) ++ L n,[]⟩ := by rfl
  have d := sweepL table 3 [] [] [false] [true] 1 (by intro L R; rfl) (n+4) (L n) []
  have e : run0 table 3 ⟨3,L n,rep [true] (n+4)⟩ = some (cfg (n+1)) := by rfl
  have b' : run0 table (1*(n+1)) ⟨2,true::L n,rep [true] (n+1)⟩ = some ⟨2,[true] ++ rep [false] (n+1) ++ L n,[]⟩ := by simpa only [List.nil_append,List.append_nil,List.cons_append] using b
  have d' : run0 table (1*(n+4)) ⟨3,[false,false,false] ++ rep [false] (n+1) ++ L n,[]⟩ = some ⟨3,L n,rep [true] (n+4)⟩ := by simpa only [List.nil_append,List.append_nil,rep,List.append_assoc,List.cons_append] using d
  exact ⟨_,by omega,join0 (join0 (join0 (join0 a b') c) d') e⟩
theorem first : run0 table 27 ⟨0,[],[]⟩ = some (cfg 0) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns table cfg 27 first epoch m hm
#print axioms never
end BB6.Agent8Raw54.LFGrowth65
