import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFGrowth61
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def O : List Bool := [true,true]
def Z : List Bool := [false,false]
def R (n : Nat) : List Bool := [false,true] ++ rep [false] (n+1) ++ [true]
def cfg (n : Nat) : Z0 := ⟨5,[],[true,false] ++ rep O (n+1) ++ R n⟩

theorem epoch (n : Nat) : ∃ t,0<t ∧ run0 table t (cfg n) = some (cfg (n+1)) := by
  have a : run0 table 4 (cfg n) = some ⟨1,[false,false,false,true],rep O (n+1) ++ R n⟩ := by rfl
  have b := sweepR table 1 [false] [] O Z 6 (by intro L R; rfl) (n+1) [false,false,true] (R n)
  have c : run0 table 5 ⟨1,[false] ++ rep Z (n+1) ++ [false,false,true],R n⟩ = some ⟨3,rep Z (n+1) ++ [false,false,true],R (n+1)⟩ := by rfl
  have d := sweepL table 3 [] [] Z O 2 (by intro L R; rfl) (n+2) [true] (R (n+1))
  have e : run0 table 2 ⟨3,[true],rep O (n+2) ++ R (n+1)⟩ = some (cfg (n+1)) := by rfl
  have b' : run0 table (6*(n+1)) ⟨1,[false,false,false,true],rep O (n+1) ++ R n⟩ = some ⟨1,[false] ++ rep Z (n+1) ++ [false,false,true],R n⟩ := by simpa only [List.nil_append,List.append_assoc,List.cons_append] using b
  have c' : run0 table 5 ⟨1,[false] ++ rep Z (n+1) ++ [false,false,true],R n⟩ = some ⟨3,rep Z (n+2) ++ [true],R (n+1)⟩ := by
    have h : rep Z (n+1) ++ [false,false,true] = rep Z (n+2) ++ [true] := by
      change rep Z (n+1) ++ (Z ++ [true]) = (Z ++ rep Z (n+1)) ++ [true]
      rw [← List.append_assoc,rep_snoc]
    rw [h] at c
    exact c
  have d' : run0 table (2*(n+2)) ⟨3,rep Z (n+2) ++ [true],R (n+1)⟩ = some ⟨3,[true],rep O (n+2) ++ R (n+1)⟩ := by simpa only [List.nil_append,List.append_assoc] using d
  exact ⟨_,by omega,join0 (join0 (join0 (join0 a b') c') d') e⟩
theorem first : run0 table 21 ⟨0,[],[]⟩ = some (cfg 0) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns table cfg 21 first epoch m hm
#print axioms never
end BB6.Agent8Raw54.LFGrowth61
