import Raw54RAClosedCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LA.M94
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent8Raw54.RAClosed

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

def P (n : Nat) : Z0 := ⟨0,[],[true,false,true] ++ rep [true,true] n⟩
def Q (m k : Nat) : Z0 := ⟨0,false::(rep [false,false] m ++ [true]),[true,false,true] ++ rep [true,true] k ++ [true]⟩
def S (k : Nat) : Z0 := ⟨0,[],[true,false,false,true] ++ rep [true,true] k ++ [true]⟩

theorem drain (k : Nat) (L : List Bool) :
  run0 table (6*k+7) ⟨1,true::L,rep [true,true] k ++ [true]⟩ =
    some ⟨3,L,rep [true,true] k ++ [true,true,true,true]⟩ := by
  have h : run0 table (4*k) ⟨1,true::L,rep [true,true] k ++ [true]⟩ =
      some ⟨1,true::(rep [false,false] k ++ L),[true]⟩ :=
    sweepR table 1 [true] [] [true,true] [false,false] 4 (fun _ _ => rfl) k L [true]
  have g (T : List Bool) : run0 table 7 ⟨1,true::T,[true]⟩ = some ⟨3,T,[true,true,true,true]⟩ := by rfl
  have d : run0 table (2*k) ⟨3,rep [false,false] k ++ L,[true,true,true,true]⟩ =
      some ⟨3,L,rep [true,true] k ++ [true,true,true,true]⟩ :=
    sweepL table 3 [] [] [false,false] [true,true] 2 (fun _ _ => rfl) k L [true,true,true,true]
  have H := join0 (join0 h (g _)) d
  rwa [show 4*k+7+2*k=6*k+7 by omega] at H

theorem onesTail (k : Nat) : rep [true,true] k ++ [true,true,true,true] = rep [true,true] (k+2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change true::true::(rep [true,true] k ++ [true,true,true,true]) = true::true::rep [true,true] (k+2)
    rw [ih]

theorem onesRotate (k : Nat) : true::rep [true,true] k = rep [true,true] k ++ [true] := by
  exact rotate true [true] k

theorem pReturn (n : Nat) : run0 table (4*n+11) (P n) = some (Q (n+1) 0) := by
  have h (T : List Bool) : run0 table 3 ⟨0,[],[true,false,true] ++ T⟩ = some ⟨1,[true,false,false,true],T⟩ := by rfl
  have g : run0 table (4*n) ⟨1,[true,false,false,true],rep [true,true] n⟩ =
      some ⟨1,true::(rep [false,false] n ++ [false,false,true]),[]⟩ := by
    simpa only [List.append_nil,List.nil_append,List.append_assoc,List.cons_append] using sweepR table 1 [true] [] [true,true] [false,false] 4 (fun _ _ => rfl) n [false,false,true] []
  have f (L : List Bool) : run0 table 8 ⟨1,true::L,[]⟩ = some ⟨0,false::L,[true,false,true,true]⟩ := by rfl
  have H := join0 (join0 (h (rep [true,true] n)) g) (f _)
  rw [show 3+4*n+8=4*n+11 by omega] at H
  have he : rep [false,false] n ++ [false,false,true] = rep [false,false] (n+1) ++ [true] := by
    change rep [false,false] n ++ ([false,false] ++ [true]) = ([false,false] ++ rep [false,false] n) ++ [true]
    rw [← List.append_assoc,rep_snoc]
  rw [he] at H
  exact H

theorem qSucc (m k : Nat) : run0 table (6*k+14) (Q (m+1) k) = some (Q m (k+2)) := by
  have h (L T : List Bool) : run0 table 3 ⟨0,false::L,[true,false,true] ++ T⟩ = some ⟨1,true::false::false::true::L,T⟩ := by rfl
  have f (L R : List Bool) : run0 table 4 ⟨3,false::false::true::false::false::L,R⟩ = some ⟨0,false::L,[true,false,true,true] ++ R⟩ := by rfl
  have H := join0 (join0 (h (rep [false,false] (m+1) ++ [true]) (rep [true,true] k ++ [true])) (drain k (false::false::true::(rep [false,false] (m+1) ++ [true])))) (f (rep [false,false] m ++ [true]) _)
  rw [show 3+(6*k+7)+4=6*k+14 by omega,onesTail] at H
  change run0 table (6*k+14) (Q (m+1) k) = some ⟨0,false::(rep [false,false] m ++ [true]),true::false::true::(rep [true,true] (k+2) ++ [true])⟩
  rw [← onesRotate]
  exact H

theorem qZero (k : Nat) : run0 table (6*k+15) (Q 0 k) = some (S (k+2)) := by
  have h (T : List Bool) : run0 table 3 ⟨0,[false,true],[true,false,true] ++ T⟩ = some ⟨1,[true,false,false,true,true],T⟩ := by rfl
  have f (R : List Bool) : run0 table 5 ⟨3,[false,false,true,true],R⟩ = some ⟨0,[],[true,false,false,true,true] ++ R⟩ := by rfl
  have H := join0 (join0 (h (rep [true,true] k ++ [true])) (drain k [false,false,true,true])) (f _)
  rw [show 3+(6*k+7)+5=6*k+15 by omega,onesTail] at H
  change run0 table (6*k+15) (Q 0 k) = some ⟨0,[],true::false::false::true::(rep [true,true] (k+2) ++ [true])⟩
  rw [← onesRotate]
  exact H

theorem sReturn (k : Nat) : run0 table (6*k+20) (S k) = some (P (k+3)) := by
  have h (T : List Bool) : run0 table 8 ⟨0,[],[true,false,false,true] ++ T⟩ = some ⟨1,[true,false,false,false,true],T⟩ := by rfl
  have f (R : List Bool) : run0 table 5 ⟨3,[false,false,false,true],R⟩ = some ⟨0,[],[true,false,true,true,true] ++ R⟩ := by rfl
  have H := join0 (join0 (h (rep [true,true] k ++ [true])) (drain k [false,false,false,true])) (f _)
  rw [show 8+(6*k+7)+5=6*k+20 by omega,onesTail] at H
  exact H

inductive Section where
  | p (n : Nat)
  | q (m k : Nat)
  | s (k : Nat)
def sect : Section → Z0
  | .p n => P n
  | .q m k => Q m k
  | .s k => S k

theorem sectionReturn (s : Section) : ∃ t s', 0 < t ∧ run0 table t (sect s) = some (sect s') := by
  cases s with
  | p n => exact ⟨4*n+11,.q (n+1) 0,by omega,pReturn n⟩
  | q m k =>
    cases m with
    | zero => exact ⟨6*k+15,.s (k+2),by omega,qZero k⟩
    | succ m => exact ⟨6*k+14,.q m (k+2),by omega,qSucc m k⟩
  | s k => exact ⟨6*k+20,.p (k+3),by omega,sReturn k⟩

theorem entry : run0 table 28 ⟨0,[],[]⟩ = some (sect (.p 3)) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  neverOfSection table _ sect (.p 3) 28 entry sectionReturn m hm
#print axioms sectionReturn
#print axioms never
end BB6.Agent8Raw54.LA.M94
