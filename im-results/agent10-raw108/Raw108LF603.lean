import SweepPumping
namespace BB6.Agent10Raw108LF603
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
abbrev P : List Bool := [true,true,true,true,true]
abbrev Z : List Bool := [false,false,false,false,false]
abbrev O : List Bool := [false,true,true,false,false]
abbrev S : List Bool := [false,true,true]
def enc : List Bool → List Bool
  | [] => []
  | false::bs => Z++enc bs
  | true::bs => O++enc bs
def inc : List Bool → List Bool
  | [] => [false]
  | false::bs => true::bs
  | true::bs => false::inc bs

def sect (bs : List Bool) : Z0 := A [false,false] (enc bs++S)
def carry (j : Nat) (bs : List Bool) : Z0 :=
  A (false::(rep P j++[false])) (enc bs++S)

theorem repAdd (w : List Bool) (a b : Nat) :
    rep w (a+b) = rep w a ++ rep w b := by
  induction a with
  | zero => simp [rep]
  | succ a ih =>
    rw [show a+1+b=(a+b)+1 by omega,rep,ih,rep]
    simp only [List.append_assoc]

theorem zeroRaw (L R : List Bool) :
    run0 table 8 (A (false::L) (Z++R)) = some (F (true::L) (O++R)) := by rfl
theorem oneRaw (L R : List Bool) :
    run0 table 5 (A (false::L) (O++R)) = some (A (false::P++L) R) := by rfl
theorem endRaw (L : List Bool) :
    run0 table 13 (A (false::L) S) = some (F (true::P++L) S) := by rfl
theorem sweepRaw (L R : List Bool) :
    run0 table 5 (F (true::P++L) R) = some (F (true::L) (Z++R)) := by rfl
theorem finish (R : List Bool) :
    run0 table 2 (F [true,false] R) = some (A [false,false] R) := by rfl

theorem drain (j : Nat) (R : List Bool) :
    run0 table (5*j+2) (F (true::(rep P j++[false])) R) =
      some (A [false,false] (rep Z j++R)) := by
  have h := sweepL table 5 [true] [] P Z 5 sweepRaw j [false] R
  have h' : run0 table (5*j) (F (true::(rep P j++[false])) R) =
      some (F [true,false] (rep Z j++R)) := by
    simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append,F] using h
  exact join0 h' (finish _)

theorem zeroCase (j : Nat) (bs : List Bool) :
    run0 table (8+(5*j+2)) (carry j (false::bs)) =
      some (A [false,false] (rep Z j++enc (true::bs)++S)) := by
  have h := zeroRaw (rep P j++[false]) (enc bs++S)
  have H := join0 h (drain j (O++enc bs++S))
  simpa only [carry,enc,List.append_assoc] using H

theorem oneCase (j : Nat) (bs : List Bool) :
    run0 table 5 (carry j (true::bs)) = some (carry (j+1) bs) := by
  simpa only [carry,enc,rep,List.append_assoc,List.cons_append] using oneRaw (rep P j++[false]) (enc bs++S)

theorem endCase (j : Nat) :
    run0 table (13+(5*(j+1)+2)) (carry j []) =
      some (A [false,false] (rep Z j++enc (inc [])++S)) := by
  have h := endRaw (rep P j++[false])
  have h' : run0 table 13 (carry j []) = some (F (true::(rep P (j+1)++[false])) S) := by
    simpa only [carry,enc,rep,List.nil_append,List.append_assoc,List.cons_append] using h
  have H := join0 h' (drain (j+1) S)
  rw [repAdd Z j 1] at H
  simpa only [inc,enc,rep,List.nil_append,List.append_nil,List.append_assoc] using H

def cost : Nat → List Bool → Nat
  | j, [] => 13+(5*(j+1)+2)
  | j, false::_ => 8+(5*j+2)
  | j, true::bs => 5+cost (j+1) bs

theorem carryAll (j : Nat) (bs : List Bool) :
    run0 table (cost j bs) (carry j bs) =
      some (A [false,false] (rep Z j++enc (inc bs)++S)) := by
  induction bs generalizing j with
  | nil => exact endCase j
  | cons b bs ih =>
    cases b with
    | false => exact zeroCase j bs
    | true =>
      have H := join0 (oneCase j bs) (ih (j+1))
      rw [repAdd Z j 1] at H
      simpa only [cost,inc,enc,rep,List.nil_append,List.append_nil,List.append_assoc] using H

theorem epoch (bs : List Bool) :
    run0 table (cost 0 bs) (sect bs) = some (sect (inc bs)) := by
  simpa only [sect,carry,rep,List.nil_append] using carryAll 0 bs

def digits : Nat → List Bool
  | 0 => [false]
  | k+1 => inc (digits k)
def family (k : Nat) := sect (digits k)
theorem entry : run0 table 30 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (k : Nat) :
    run0 table (cost 0 (digits k)) (family k) = some (family (k+1)) :=
  epoch (digits k)
theorem positive (j : Nat) (bs : List Bool) : 0 < cost j bs := by
  cases bs with
  | nil => simp [cost] <;> omega
  | cons b bs => cases b <;> simp [cost] <;> omega

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 30 (fun k => cost 0 (digits k)) entry
    (fun k => positive 0 (digits k)) growth m hm
#print axioms carryAll
#print axioms growth
#print axioms never
end BB6.Agent10Raw108LF603
