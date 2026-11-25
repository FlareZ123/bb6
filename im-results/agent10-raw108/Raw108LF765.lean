import SweepPumping
namespace BB6.Agent10Raw108LF765
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev E (L R : List Bool) : Z0 := ⟨4,L,R⟩
abbrev P : List Bool := [true,true,true]
abbrev Z : List Bool := [false,false,false]
abbrev O : List Bool := [false,true,false]
abbrev S : List Bool := [false,true]
abbrev J : List Bool := [false,true,true,false,false]
abbrev K : List Bool := [false,true,true,false]
abbrev W : List Bool := [true,true,true,true,true]
def enc : List Bool → List Bool
  | [] => []
  | false::bs => Z++enc bs
  | true::bs => O++enc bs
def inc : List Bool → List Bool
  | [] => [false]
  | false::bs => true::bs
  | true::bs => false::inc bs

def sect (bs : List Bool) : Z0 := E J (enc bs++S)
def carry (j : Nat) (bs : List Bool) : Z0 :=
  E (K++rep P j++[false]) (enc bs++S)
theorem repAdd (w : List Bool) (a b : Nat) :
    rep w (a+b) = rep w a ++ rep w b := by
  induction a with
  | zero => simp [rep]
  | succ a ih =>
    rw [show a+1+b=(a+b)+1 by omega,rep,ih,rep]
    simp only [List.append_assoc]

theorem oneRaw (L R : List Bool) :
    run0 table 17 (E (K++L) (O++R)) = some (E (K++P++L) R) := by rfl
theorem zeroRaw (L R : List Bool) :
    run0 table 12 (E (K++L) (Z++R)) = some (E (false::W++L) (false::R)) := by rfl
theorem endOne (L : List Bool) :
    run0 table 17 (E (K++L) S) = some (E (K++P++L) []) := by rfl
theorem endZero (L : List Bool) :
    run0 table 12 (E (K++L) []) = some (E (false::W++L) []) := by rfl
theorem startReturn (L R : List Bool) :
    run0 table 1 (E (false::W++L) R) = some (A (W++L) (true::R)) := by rfl
theorem sweepRaw (L R : List Bool) :
    run0 table 3 (A (W++P++L) R) = some (A (W++L) (Z++R)) := by rfl
theorem finish (R : List Bool) :
    run0 table 21 (A (W++[false]) R) = some (E J (false::R)) := by rfl

theorem shiftZero (j : Nat) (R : List Bool) :
    false::(rep Z j++R) = rep Z j++false::R := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [rep,Z,List.cons_append,List.nil_append]
    rw [ih]
theorem drain (j : Nat) (R : List Bool) :
    run0 table (1+3*j+21) (E (false::W++rep P j++[false]) R) =
      some (E J (rep Z j++false::true::R)) := by
  have h := startReturn (rep P j++[false]) R
  have h' := sweepL table 0 W [] P Z 3 sweepRaw j [false] (true::R)
  have h'' : run0 table (3*j) (A (W++(rep P j++[false])) (true::R)) =
      some (A (W++[false]) (rep Z j++true::R)) := by
    simpa only [List.append_assoc,List.nil_append,List.append_nil,A] using h'
  have H := join0 (join0 h h'') (finish (rep Z j++true::R))
  rw [shiftZero] at H
  simpa only [List.append_assoc,List.cons_append] using H

theorem zeroCase (j : Nat) (bs : List Bool) :
    run0 table (12+(1+3*j+21)) (carry j (false::bs)) =
      some (E J (rep Z j++enc (true::bs)++S)) := by
  have h := zeroRaw (rep P j++[false]) (enc bs++S)
  have H := join0 h (drain j (false::(enc bs++S)))
  simpa only [carry,enc,List.append_assoc,O,List.cons_append,List.nil_append] using H

theorem oneCase (j : Nat) (bs : List Bool) :
    run0 table 17 (carry j (true::bs)) = some (carry (j+1) bs) := by
  simpa only [carry,enc,rep,List.append_assoc] using oneRaw (rep P j++[false]) (enc bs++S)

theorem endCase (j : Nat) :
    run0 table (17+12+(1+3*(j+1)+21)) (carry j []) =
      some (E J (rep Z j++enc (inc [])++S)) := by
  have h := endOne (rep P j++[false])
  have h' := endZero (rep P (j+1)++[false])
  have h0 : run0 table 17 (carry j []) = some (E (K++(rep P (j+1)++[false])) []) := by
    simpa only [carry,enc,rep,List.nil_append,List.append_assoc] using h
  have H := join0 (join0 h0 h') (drain (j+1) [])
  rw [repAdd Z j 1] at H
  simpa only [enc,inc,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,Z,S] using H

def cost : Nat → List Bool → Nat
  | j, [] => 17+12+(1+3*(j+1)+21)
  | j, false::_ => 12+(1+3*j+21)
  | j, true::bs => 17+cost (j+1) bs
theorem carryAll (j : Nat) (bs : List Bool) :
    run0 table (cost j bs) (carry j bs) =
      some (E J (rep Z j++enc (inc bs)++S)) := by
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
  simpa only [sect,carry,rep,List.nil_append,List.append_nil,K,J,List.cons_append] using carryAll 0 bs

def digits : Nat → List Bool
  | 0 => []
  | k+1 => inc (digits k)
def family (k : Nat) := sect (digits k)
theorem entry : run0 table 50 ⟨0,[],[]⟩ = some (family 0) := by rfl
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
end BB6.Agent10Raw108LF765
