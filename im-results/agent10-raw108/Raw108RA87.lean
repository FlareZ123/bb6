import SweepPumping

namespace BB6.Agent10Raw108RA87
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Raw108/1RA leaf 87. Four-cell digits 0000 and 0010, least significant
first, followed by 001. A carry scans the digits and overflow adds a digit.
All local phases are exact runs over arbitrary untouched tails. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev P : List Bool := [true,true]
abbrev Z : List Bool := [false,false]
abbrev S : List Bool := [false,false,true]
abbrev B : List Bool := [true,false]
def enc : List Bool → List Bool
  | [] => []
  | b::bs => [false,false,b,false] ++ enc bs
def inc : List Bool → List Bool
  | [] => [false]
  | false::bs => true::bs
  | true::bs => false::inc bs

def sect (bs : List Bool) : Z0 := A B (enc bs ++ S)
def carry (j : Nat) (bs : List Bool) : Z0 :=
  A (false::(rep P j ++ [false])) (enc bs ++ S)

theorem repAdd (w : List Bool) (a b : Nat) :
    rep w (a+b) = rep w a ++ rep w b := by
  induction a with
  | zero => simp [rep]
  | succ a ih =>
    rw [show a+1+b=(a+b)+1 by omega,rep,ih,rep]
    simp only [List.append_assoc]

theorem start_epoch (bs : List Bool) :
    run0 table 2 (sect bs) = some (carry 0 bs) := by rfl

theorem pair_step (L R : List Bool) :
    run0 table 2 (A (P++L) R) = some (A L (Z++R)) := by rfl

theorem drain (j : Nat) (R : List Bool) :
    run0 table (2*j) (A (rep P j++B) R) = some (A B (rep Z j++R)) := by
  simpa only [List.nil_append,List.append_nil,List.append_assoc] using
    sweepL table 0 [] [] P Z 2 pair_step j B R

theorem zero_raw (L R : List Bool) :
    run0 table 8 (A (false::L) ([false,false,false,false]++R)) =
      some (A ([true,true,true]++L) ([true,false]++R)) := by rfl

theorem one_raw (L R : List Bool) :
    run0 table 22 (A (false::L) ([false,false,true,false,false,false]++R)) =
      some (A ([false,true,true,true,true]++L) ([false,false]++R)) := by rfl

theorem end_raw (L : List Bool) :
    run0 table 30 (A (false::L) S) =
      some (A ([true,true,true,true,true,true,true]++L) [true]) := by rfl

theorem pairs_true (j : Nat) :
    rep P j ++ B = true::(rep P j ++ [false]) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change P ++ (rep P j ++ B) = true::(P ++ (rep P j ++ [false]))
    rw [ih]
    rfl

theorem zero_case (j : Nat) (bs : List Bool) :
    run0 table (8+2*(j+1)) (carry j (false::bs)) =
      some (A B (rep Z j ++ enc (true::bs) ++ S)) := by
  have h := zero_raw (rep P j ++ [false]) (enc bs++S)
  have hd := drain (j+1) ([true,false]++enc bs++S)
  have eqL : rep P (j+1) ++ B = [true,true,true] ++ rep P j ++ [false] := by
    simp only [rep,List.append_assoc,pairs_true]
    rfl
  rw [eqL] at hd
  have H := join0 h hd
  rw [repAdd Z j 1] at H
  simpa only [carry,enc,rep,Z,List.nil_append,List.append_nil,List.append_assoc,List.cons_append,P,S,B] using H

theorem one_case (j : Nat) (bs : List Bool) :
    run0 table 22 (carry j (true::bs)) = some (carry (j+2) bs) := by
  cases bs with
  | nil =>
    have H := one_raw (rep P j++[false]) [true]
    simpa only [carry,enc,rep,show j+2=(j+1)+1 by omega,List.nil_append,List.append_nil,List.append_assoc,List.cons_append,P,S,B] using H
  | cons b bs =>
    have H := one_raw (rep P j++[false]) (b::false::(enc bs++S))
    simpa only [carry,enc,rep,show j+2=(j+1)+1 by omega,List.nil_append,List.append_nil,List.append_assoc,List.cons_append,P,S,B] using H

theorem end_case (j : Nat) :
    run0 table (30+2*(j+3)) (carry j []) =
      some (A B (rep Z j ++ enc (inc []) ++ S)) := by
  have h := end_raw (rep P j++[false])
  have hd := drain (j+3) [true]
  have eqL : rep P (j+3) ++ B = [true,true,true,true,true,true,true] ++ rep P j ++ [false] := by
    simp only [rep,List.append_assoc,pairs_true]
    rfl
  rw [eqL] at hd
  have H := join0 h hd
  rw [repAdd Z j 3] at H
  simpa only [carry,inc,enc,rep,Z,List.nil_append,List.append_nil,List.append_assoc,List.cons_append,P,S,B] using H

def cost : Nat → List Bool → Nat
  | j, [] => 30+2*(j+3)
  | j, false::_ => 8+2*(j+1)
  | j, true::bs => 22+cost (j+2) bs

theorem carry_all (j : Nat) (bs : List Bool) :
    run0 table (cost j bs) (carry j bs) =
      some (A B (rep Z j ++ enc (inc bs) ++ S)) := by
  induction bs generalizing j with
  | nil => exact end_case j
  | cons b bs ih =>
    cases b with
    | false => exact zero_case j bs
    | true =>
      have H := join0 (one_case j bs) (ih (j+2))
      rw [repAdd Z j 2] at H
      simpa only [cost,inc,enc,rep,Z,List.nil_append,List.append_nil,List.append_assoc,List.cons_append,P,S,B] using H

theorem epoch (bs : List Bool) :
    run0 table (2+cost 0 bs) (sect bs) = some (sect (inc bs)) := by
  simpa only [rep,List.nil_append,sect] using join0 (start_epoch bs) (carry_all 0 bs)

def digits : Nat → List Bool
  | 0 => [false]
  | k+1 => inc (digits k)
def family (k : Nat) : Z0 := sect (digits k)

theorem entry : run0 table 48 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (k : Nat) :
    run0 table (2+cost 0 (digits k)) (family k) = some (family (k+1)) :=
  epoch (digits k)

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 48 (fun k => 2+cost 0 (digits k)) entry
    (by intro k; omega) growth m hm

#print axioms carry_all
#print axioms entry
#print axioms growth
#print axioms never

end BB6.Agent10Raw108RA87
