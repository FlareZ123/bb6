import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFGrowth0
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

def O : List Bool := [true]
def Z : List Bool := [false]
def Z4 : List Bool := [false,false,false,false]
def cfg (k : Nat) (R : List Bool) : Z0 := ⟨0,false::rep O k,R⟩

theorem rep_add (P : List Bool) (n m : Nat) : rep P (n+m) = rep P n ++ rep P m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [show n+1+m=n+m+1 by omega]; simp only [rep,ih,List.append_assoc]

theorem rep_four (n : Nat) : rep Z (4*n) = rep Z4 n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 4*(n+1)=4+4*n by omega,rep_add,ih]; rfl

theorem prep (k : Nat) (T : List Bool) :
    run0 table 6 (cfg (k+2) (false::false::false::T)) = some ⟨4,rep O (k+3),false::true::true::T⟩ := by
  simp only [cfg,rep,O,List.cons_append,List.nil_append]
  rfl

theorem reset_tail (k : Nat) (T : List Bool) :
    run0 table (k+23+2) (cfg (k+2) (false::false::false::T)) =
    some (cfg 2 (false::false::true::true::(rep Z k ++ true::true::T))) := by
  have a := prep k T
  have b := sweepL table 4 [] [] O Z 1 (by intro L R; rfl) (k+3) [] (false::true::true::T)
  simp only [List.nil_append,List.append_nil,Nat.one_mul] at b
  have E : rep Z (k+3) ++ false::true::true::T = false::false::false::false::(rep Z k ++ true::true::T) := by
    clear a b
    induction k with
    | zero => rfl
    | succ k ih =>
      change false :: (rep Z (k+3) ++ _) = false :: (false::false::false::false::(rep Z k ++ _))
      rw [ih]
  rw [E] at b
  have c : run0 table 16 ⟨4,[],false::false::false::false::(rep Z k ++ true::true::T)⟩ =
      some (cfg 2 (false::false::true::true::(rep Z k ++ true::true::T))) := by rfl
  have H := join0 (join0 a b) c
  rw [show 6+(k+3)+16=k+23+2 by omega] at H
  exact H

theorem reset_blank (k : Nat) :
    run0 table (k+25) (cfg (k+2) [false,false]) =
    some (cfg 2 (false::false::true::true::(rep Z k ++ [true,true]))) := by
  have a : run0 table 6 (cfg (k+2) [false,false]) = some ⟨4,rep O (k+3),[false,true,true]⟩ := by
    simp only [cfg,rep,O,List.cons_append,List.nil_append]
    rfl
  have b := sweepL table 4 [] [] O Z 1 (by intro L R; rfl) (k+3) [] [false,true,true]
  simp only [List.nil_append,List.append_nil,Nat.one_mul] at b
  have E : rep Z (k+3) ++ [false,true,true] = false::false::false::false::(rep Z k ++ [true,true]) := by
    clear a b
    induction k with
    | zero => rfl
    | succ k ih =>
      change false :: (rep Z (k+3) ++ _) = false :: (false::false::false::false::(rep Z k ++ _))
      rw [ih]
  rw [E] at b
  have c : run0 table 16 ⟨4,[],false::false::false::false::(rep Z k ++ [true,true])⟩ =
      some (cfg 2 (false::false::true::true::(rep Z k ++ [true,true]))) := by rfl
  have H := join0 (join0 a b) c
  rw [show 6+(k+3)+16=k+25 by omega] at H
  exact H

theorem advance (k : Nat) (T : List Bool) :
    run0 table 8 (cfg k (false::false::true::true::T)) = some (cfg (k+2) (false::true::T)) := by rfl

theorem shave (k : Nat) (T : List Bool) :
    run0 table 14 (cfg k (false::true::false::false::false::false::T)) = some (cfg (k+2) (false::false::true::true::T)) := by rfl

theorem drain (k n : Nat) (T : List Bool) :
    run0 table (22*n) (cfg k (false::false::true::true::(rep Z4 n ++ T))) =
    some (cfg (k+4*n) (false::false::true::true::T)) := by
  induction n generalizing k with
  | zero => simp [rep,run0]
  | succ n ih =>
    have a := advance k (Z4 ++ rep Z4 n ++ T)
    have b := shave (k+2) (rep Z4 n ++ T)
    have H := join0 (join0 a b) (ih (k+2+2))
    rw [show 8+14+22*n=22*(n+1) by omega,show k+2+2+4*n=k+4*(n+1) by omega] at H
    simpa only [rep,List.append_assoc,Z4,List.cons_append,List.nil_append] using H

theorem tip (k : Nat) : run0 table 22 (cfg k [false,true,false,false,true,true]) =
    some (cfg (k+2) [false,false,false,true,true]) := by rfl

theorem seven (k : Nat) (T : List Bool) : run0 table 7 (cfg k (false::true::true::T)) =
    some (cfg (k+1) (false::false::T)) := by rfl

theorem finish (k : Nat) : run0 table 30 (cfg k [false,false,true,true,true,true,true,true]) =
    some (cfg (k+6) [false,false]) := by
  exact join0 (join0 (join0 (advance k [true,true,true,true]) (seven (k+2) [true,true,true])) (advance (k+2+1) [true])) (seven (k+2+1+2) [])

def family (n : Nat) : Z0 := cfg (8*n+8) [false,false]

theorem first : run0 table 86 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (104*n+190) (family n) = some (family (n+1)) := by
  have a := reset_blank (8*n+6)
  have ea : rep Z (8*n+6) ++ [true,true] = rep Z4 (2*n+1) ++ [false,false,true,true] := by
    rw [show 8*n+6=4*(2*n+1)+2 by omega,rep_add,rep_four]
    simp only [List.append_assoc]
    rfl
  rw [ea] at a
  have b := drain 2 (2*n+1) [false,false,true,true]
  have c := join0 (advance (2+4*(2*n+1)) [false,false,true,true]) (tip (2+4*(2*n+1)+2))
  have H := join0 (join0 a b) c
  have d := reset_tail (8*n+8) [true,true]
  have eb : rep Z (8*n+8) ++ true::true::[true,true] = rep Z4 (2*n+2) ++ [true,true,true,true] := by
    rw [show 8*n+8=4*(2*n+2) by omega,rep_four]
  rw [eb] at d
  have e := drain 2 (2*n+2) [true,true,true,true]
  have f := finish (2+4*(2*n+2))
  rw [show 2+4*(2*n+1)+2+2=8*n+8+2 by omega] at H
  have G := join0 (join0 (join0 H d) e) f
  rw [show 8*n+6+25+22*(2*n+1)+(8+22)+(8*n+8+23+2)+22*(2*n+2)+30=104*n+190 by omega] at G
  simpa only [family,show 8*n+6+2=8*n+8 by omega,show 2+4*(2*n+2)+6=8*(n+1)+8 by omega] using G

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 86 (fun n => 104*n+190) first (by intro n; omega) growth m hm
#print axioms never
end BB6.Agent8Raw54.LFGrowth0
