import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFGrowth38
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

def U : List Bool := [true,true,true]
def Z : List Bool := [false,false,false]
def P : List Bool := [true,false,false]
def Q : List Bool := [true,false,false,false]
def L : List Bool := [true,true,true,false]
def M : List Bool := [true,true,false]
def cfg (n : Nat) : Z0 := ⟨5,[],P ++ rep U (n+1) ++ [true,true]⟩
def mid (n : Nat) : Z0 := ⟨5,[],Q ++ rep U (n+3) ++ [true]⟩

theorem rep_add (P : List Bool) (n m : Nat) : rep P (n+m) = rep P n ++ rep P m := by
  induction m with
  | zero => simp [rep]
  | succ m ih => rw [Nat.add_succ]; simp only [rep,ih]; rw [← List.append_assoc,← rep_snoc,List.append_assoc]

theorem phase1 (n : Nat) : ∃ t,0<t ∧ run0 table t (cfg n) = some (mid n) := by
  have a : run0 table 8 (cfg n) = some ⟨5,true::L,[true,false] ++ rep U n ++ [true,true]⟩ := by cases n <;> rfl
  have b := sweepR table 5 [true] [true,false] U Z 7 (by intro L R; rfl) n L [true,true]
  have c : run0 table 21 ⟨5,[true] ++ rep Z n ++ L,[true,false,true,true]⟩ = some ⟨3,rep [false] 8 ++ rep Z n ++ L,[true,true]⟩ := by rfl
  have d : run0 table 8 ⟨3,rep [false] 8 ++ rep Z n ++ L,[true,true]⟩ = some ⟨3,rep Z n ++ L,rep [true] 10⟩ := by rfl
  have e := sweepL table 3 [] [] Z U 3 (by intro L R; rfl) n L (rep [true] 10)
  have f : run0 table 4 ⟨3,L,rep U n ++ rep [true] 10⟩ = some (mid n) := by
    unfold mid
    rw [rep_add U n 3]
    simp only [List.append_assoc]
    rfl
  simp only [List.nil_append,List.append_assoc,List.cons_append] at b e
  exact ⟨_,by omega,join0 (join0 (join0 (join0 (join0 a b) c) d) e) f⟩

theorem phase2 (n : Nat) : ∃ t,0<t ∧ run0 table t (mid n) = some (cfg (n+3)) := by
  have a : run0 table 7 (mid n) = some ⟨5,true::M,[true,false] ++ rep U (n+3)⟩ := by
    unfold mid
    have h : rep U (n+3) ++ [true] = true::rep U (n+3) := by
      generalize n+3=k
      induction k with
      | zero => rfl
      | succ k ih => simp only [rep,List.append_assoc,ih]; rfl
    rw [List.append_assoc,h]
    rfl
  have b := sweepR table 5 [true] [true,false] U Z 7 (by intro L R; rfl) (n+3) M []
  have c : run0 table 4 ⟨5,[true] ++ rep Z (n+3) ++ M,[true,false]⟩ = some ⟨3,rep [false] 5 ++ rep Z (n+3) ++ M,[]⟩ := by rfl
  have d : run0 table 5 ⟨3,rep [false] 5 ++ rep Z (n+3) ++ M,[]⟩ = some ⟨3,rep Z (n+3) ++ M,rep [true] 5⟩ := by rfl
  have e := sweepL table 3 [] [] Z U 3 (by intro L R; rfl) (n+3) M (rep [true] 5)
  have f : run0 table 3 ⟨3,M,rep U (n+3) ++ rep [true] 5⟩ = some (cfg (n+3)) := by
    unfold cfg
    rw [rep_add U (n+3) 1]
    simp only [List.append_assoc]
    rfl
  simp only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append] at b e
  exact ⟨_,by omega,join0 (join0 (join0 (join0 (join0 a b) c) d) e) f⟩

def family (n : Nat) : Z0 := cfg (3*n+2)
theorem first : run0 table 78 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem next (n : Nat) : ∃ t,0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  obtain ⟨t,ht,h⟩ := phase1 (3*n+2)
  obtain ⟨u,hu,g⟩ := phase2 (3*n+2)
  refine ⟨t+u,by omega,?_⟩
  unfold family
  rw [show 3*(n+1)+2=3*n+2+3 by omega]
  exact join0 h g
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns table family 78 first next m hm
#print axioms never
end BB6.Agent8Raw54.LFGrowth38
