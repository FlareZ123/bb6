import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFGrowth63
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,true,2⟩)
  | _,_ => none

def O : List Bool := [true,true]
def Z : List Bool := [false,false]
def L : List Bool := [true,false,true,false,false,true]
def M : List Bool := [true,false] ++ L
def cfg (n : Nat) : Z0 := ⟨5,L,[true,false,true] ++ rep O n ++ [true]⟩

theorem rot (n : Nat) : rep O n ++ [true] = true::rep O n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,List.append_assoc,ih]; rfl

theorem epoch (n : Nat) : ∃ t,0<t ∧ run0 table t (cfg n) = some (cfg (n+1)) := by
  have a : run0 table 3 (cfg n) = some ⟨2,true::M,rep O n ++ [true]⟩ := by rfl
  have b := sweepR table 2 [true] [] O Z 2 (by intro L R; rfl) n M [true]
  have c : run0 table 3 ⟨2,[true] ++ rep Z n ++ M,[true]⟩ = some ⟨3,[false,false,false,false] ++ rep Z n ++ M,[]⟩ := by rfl
  have d := sweepL table 3 [] [] Z O 2 (by intro L R; rfl) (n+2) M []
  have e : run0 table 2 ⟨3,M,rep O (n+2)⟩ = some (cfg (n+1)) := by
    unfold cfg
    rw [List.append_assoc,rot]
    rfl
  have b' : run0 table (2*n) ⟨2,true::M,rep O n ++ [true]⟩ = some ⟨2,[true] ++ rep Z n ++ M,[true]⟩ := by simpa only [List.nil_append,List.cons_append] using b
  have d' : run0 table (2*(n+2)) ⟨3,[false,false,false,false] ++ rep Z n ++ M,[]⟩ = some ⟨3,M,rep O (n+2)⟩ := by
    simpa only [List.nil_append,List.append_nil,rep,List.append_assoc,Z,List.cons_append] using d
  exact ⟨_,by omega,join0 (join0 (join0 (join0 a b') c) d') e⟩
theorem first : run0 table 26 ⟨0,[],[]⟩ = some (cfg 0) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns table cfg 26 first epoch m hm
#print axioms never
end BB6.Agent8Raw54.LFGrowth63
