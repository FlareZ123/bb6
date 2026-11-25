import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.Growth50Pair
open BB6Coverage BB6Coverage.Agent31Pump

def table (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some (if v then ⟨true,false,3⟩ else ⟨false,false,2⟩))
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | _,_ => none

def cfg (n : Nat) : Z0 := ⟨0,[false,false,false] ++ rep [true] (n+1),rep [true,true] (n+1)⟩
def mid (n j m : Nat) : Z0 := ⟨0,[true,false,false,true] ++ rep [false,false] j ++ [true,false,false] ++ rep [true] (n+1),true::rep [true,true] m⟩
def stage (v : Bool) : Nat := if v then 8 else 10

theorem firstPhase (v : Bool) (n : Nat) : run0 (table v) (2*n+12) (cfg n) = some (mid n n 0) := by
  have a : run0 (table v) 1 (cfg n) = some ⟨1,[true,true,false,false] ++ rep [true] (n+1),rep [true,true] n ++ [true]⟩ := by
    have h : rep [true,true] n ++ [true] = true :: rep [true,true] n := by
      induction n with
      | zero => rfl
      | succ n ih => simp only [rep,List.append_assoc]; rw [ih]; rfl
    rw [h]
    cases v <;> rfl
  have b := sweepR (table v) 1 [true] [] [true,true] [false,false] 2 (by intro L R; cases v <;> rfl) n ([true,false,false] ++ rep [true] (n+1)) [true]
  have c : run0 (table v) 11 ⟨1,[true] ++ rep [false,false] n ++ ([true,false,false] ++ rep [true] (n+1)),[true]⟩ = some (mid n n 0) := by
    cases n <;> cases v <;> simp only [mid,rep,List.append_assoc] <;> rfl
  simp only [List.nil_append,List.append_assoc] at b
  have H := join0 (join0 a b) c
  rw [show 2*n+12 = 1+2*n+11 by omega]
  exact H

theorem midStep (v : Bool) (n j m : Nat) : run0 (table v) (stage v) (mid n (j+1) m) = some (mid n j (m+1)) := by
  cases v <;> rfl

theorem midLast (v : Bool) (n m : Nat) : run0 (table v) (stage v+1) (mid n 0 m) = some ⟨0,[false,false,false] ++ rep [true] (n+2),rep [true,true] (m+2)⟩ := by
  cases v <;> rfl

theorem drain (v : Bool) (n j m : Nat) : ∃ t, 0<t ∧ run0 (table v) t (mid n j m) = some ⟨0,[false,false,false] ++ rep [true] (n+2),rep [true,true] (m+j+2)⟩ := by
  induction j generalizing m with
  | zero => exact ⟨stage v+1,by omega,midLast v n m⟩
  | succ j ih =>
    obtain ⟨t,ht,h⟩ := ih (m+1)
    have H := join0 (midStep v n j m) h
    refine ⟨stage v+t,by omega,?_⟩
    rw [show m+(j+1)+2 = (m+1)+j+2 by omega]
    exact H

theorem epoch (v : Bool) (n : Nat) : ∃ t, 0<t ∧ run0 (table v) t (cfg n) = some (cfg (n+1)) := by
  obtain ⟨t,ht,h⟩ := drain v n n 0
  simp only [Nat.zero_add] at h
  exact ⟨2*n+12+t,by omega,join0 (firstPhase v n) h⟩

theorem first (v : Bool) : run0 (table v) 11 ⟨0,[],[]⟩ = some (cfg 0) := by cases v <;> rfl

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns (table v) cfg 11 (first v) (epoch v) m hm
#print axioms never
end BB6.Agent8Raw54.Growth50Pair
