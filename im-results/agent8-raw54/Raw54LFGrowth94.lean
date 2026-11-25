import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFGrowth94
open BB6Coverage BB6Coverage.Agent31Pump

inductive Kind where | k94 | k97 | k98

def table (v : Kind) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some (match v with | .k94 => ⟨false,false,1⟩ | _ => ⟨false,false,5⟩))
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | 5,true => some (some (match v with | .k97 => ⟨true,true,0⟩ | _ => ⟨true,true,5⟩))
  | _,_ => none

def O : List Bool := [true,true,true,true]
def Z : List Bool := [false,false,false,false]
def P : List Bool := [true,false,false,false,true,true]
def X : List Bool := [true,false,true]
def cfg (n : Nat) : Z0 := ⟨5,[],P ++ rep Z n ++ [true,true]⟩
def extra : Kind → Nat | .k97 => 2 | _ => 0

theorem rot (b : Bool) (n : Nat) (R : List Bool) : rep [b,b,b,b] n ++ b::R = b::(rep [b,b,b,b] n ++ R) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,List.append_assoc]; rw [ih]; rfl

theorem epoch (v : Kind) (n : Nat) : ∃ t,0<t ∧ run0 (table v) t (cfg n) = some (cfg (n+1)) := by
  have a : run0 (table v) 7 (cfg n) = some ⟨5,true::X,X ++ rep Z n ++ [true,true]⟩ := by cases v <;> rfl
  have b := sweepR (table v) 5 [true] X Z O (18+2*extra v) (by intro L R; cases v <;> rfl) n [true,false,true] [true,true]
  have c : run0 (table v) (9+extra v) ⟨5,[true] ++ rep O n ++ [true,false,true],X ++ [true,true]⟩ = some ⟨5,[true,true,true,true] ++ rep O n ++ [true,false,true],[true,false]⟩ := by cases v <;> rfl
  have d : run0 (table v) (9+extra v) ⟨5,[true,true,true,true] ++ rep O n ++ [true,false,true],[true,false]⟩ = some ⟨4,[true,true,true] ++ rep O n ++ [true,false,true],[false,false,false,true,true]⟩ := by cases v <;> rfl
  have h : [true,true,true] ++ rep O n ++ [true,false,true] = rep O (n+1) ++ [false,true] := by
    simp only [List.append_assoc]
    change [true,true,true] ++ (rep [true,true,true,true] n ++ true::[false,true]) = _
    rw [rot]
    rfl
  rw [h] at d
  have e := sweepL (table v) 4 [] [] O Z 4 (by intro L R; cases v <;> rfl) (n+1) [false,true] [false,false,false,true,true]
  have f : run0 (table v) 1 ⟨4,[false,true],rep Z (n+1) ++ [false,false,false,true,true]⟩ = some ⟨5,[true],true::(rep Z (n+1) ++ [false,false,false,true,true])⟩ := by cases v <;> rfl
  have g : run0 (table v) (10+extra v) ⟨5,[true],true::(rep Z (n+1) ++ [false,false,false,true,true])⟩ = some (cfg (n+1)) := by
    change run0 (table v) _ ⟨5,[true],true::(rep [false,false,false,false] (n+1) ++ false::false::false::[true,true])⟩ = _
    rw [rot,rot,rot]
    cases v <;> rfl
  simp only [List.nil_append,List.append_assoc,List.cons_append] at b e
  have H := join0 (join0 (join0 (join0 (join0 (join0 a b) c) d) e) f) g
  exact ⟨_,by omega,H⟩
def entry : Kind → Nat | .k97 => 34 | _ => 32
theorem first (v : Kind) : run0 (table v) (entry v) ⟨0,[],[]⟩ = some (cfg 0) := by cases v <;> rfl
theorem never (v : Kind) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns (table v) cfg (entry v) (first v) (epoch v) m hm
#print axioms never
end BB6.Agent8Raw54.LFGrowth94
