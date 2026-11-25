import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.Growth49
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

def cfg (n : Nat) : Z0 := ⟨0,false::rep [true] n,[]⟩

theorem phase1 (n : Nat) : run0 table (4*n+20) (cfg n) = some ⟨0,false::rep [true] (n+4),[true]⟩ := by
  have a : run0 table 6 (cfg n) = some ⟨4,rep [true] (n+1),[false,true,true]⟩ := by rfl
  have b := sweepL table 4 [] [] [true] [false] 1 (by intro L R; rfl) (n+1) [] [false,true,true]
  have c : run0 table 2 ⟨4,[],rep [false] (n+1) ++ [false,true,true]⟩ = some ⟨2,[true,true],rep [false] (n+2) ++ [true,true]⟩ := by
    have h := rep_snoc [false] (n+1)
    change _ = some (⟨2,[true,true], [false] ++ rep [false] (n+1) ++ [true,true]⟩ : Z0)
    rw [← h]
    simp only [List.append_assoc]; rfl
  have d := sweepR table 2 [true,true] [] [false] [true] 3 (by intro L R; rfl) (n+2) [] [true,true]
  have e : run0 table 5 ⟨2,[true,true] ++ rep [true] (n+2),[true,true]⟩ = some ⟨0,false::rep [true] (n+4),[true]⟩ := by rfl
  simp only [List.nil_append,List.append_nil, Nat.one_mul] at b d
  have H := join0 (join0 (join0 (join0 a b) c) d) e
  rw [show 4*n+20 = 6+(n+1)+2+3*(n+2)+5 by omega]
  exact H

theorem phase2 (n : Nat) : run0 table 11 ⟨0,false::rep [true] (n+4),[true]⟩ = some ⟨0,false::rep [true] (n+7),[true,true]⟩ := by rfl

theorem phase3 (n : Nat) : run0 table 3 ⟨0,false::rep [true] (n+7),[true,true]⟩ = some (cfg (n+10)) := by rfl

theorem epoch (n : Nat) : run0 table (4*n+34) (cfg n) = some (cfg (n+10)) := by
  have H := join0 (join0 (phase1 n) (phase2 n)) (phase3 n)
  rw [show 4*n+34 = 4*n+20+11+3 by omega]
  exact H

def family (n : Nat) : Z0 := cfg (10*n+10)
theorem first : run0 table 34 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem next (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  refine ⟨4*(10*n+10)+34,by omega,?_⟩
  unfold family
  rw [show 10*(n+1)+10 = (10*n+10)+10 by omega]
  exact epoch _

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns table family 34 first next m hm
#print axioms never
end BB6.Agent8Raw54.Growth49
