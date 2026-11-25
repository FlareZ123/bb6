import SweepPumping

namespace BB6.Agent10Raw108RC43

open BB6Coverage BB6Coverage.Agent31Pump

set_option maxRecDepth 100000

set_option maxHeartbeats 0

/-- Raw108/0RC leaf 43, E0=0RA. Six symbolic sweeps give a four-one / one-block growth epoch. -/

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | _,_ => none

def sect (n : Nat) (R : List Bool) : Z0 := ⟨0,[],[true,true] ++ rep [true,true] n ++ [true,false,false,false,false,false,false,true,true,true] ++ R⟩

theorem phase0 (n : Nat) (R : List Bool) : run0 table 17 ⟨0,[],[true,true] ++ rep [true,true] n ++ [true,false,false,false,false,false,false,true,true,true] ++ R⟩ = some ⟨1,[false,true],[false,true,true] ++ rep [true,true] n ++ [true,false,false,false,false,false,false,true,true,true] ++ R⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨1,[false] ++ L,[false,true,true] ++ [true,true] ++ R⟩ = some ⟨1,[false] ++ [true,true] ++ L,[false,true,true] ++ R⟩ := by rfl

theorem phase1 (n : Nat) (R : List Bool) : run0 table (8*n) ⟨1,[false,true],[false,true,true] ++ rep [true,true] n ++ [true,false,false,false,false,false,false,true,true,true] ++ R⟩ = some ⟨1,[false] ++ rep [true,true] n ++ [true],[false,true,true,true,false,false,false,false,false,false,true,true,true] ++ R⟩ := by
  simpa only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using sweepR table 1 [false] [false,true,true] [true,true] [true,true] 8 local1 n ([true]) ([true,false,false,false,false,false,false,true,true,true] ++ R)

theorem phase2 (n : Nat) (R : List Bool) : run0 table 46 ⟨1,[false] ++ rep [true,true] n ++ [true],[false,true,true,true,false,false,false,false,false,false,true,true,true] ++ R⟩ = some ⟨0,[true,true,true] ++ rep [true,true] n ++ [true],[false,false,true,true,true,true,true,false,true,true,true] ++ R⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨0,[true,true,true] ++ [true,true] ++ L,R⟩ = some ⟨0,[true,true,true] ++ L,[true,true] ++ R⟩ := by rfl

theorem phase3 (n : Nat) (R : List Bool) : run0 table (2*n) ⟨0,[true,true,true] ++ rep [true,true] n ++ [true],[false,false,true,true,true,true,true,false,true,true,true] ++ R⟩ = some ⟨0,[true,true,true,true],rep [true,true] n ++ [false,false,true,true,true,true,true,false,true,true,true] ++ R⟩ := by
  simpa only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using sweepL table 0 [true,true,true] [] [true,true] [true,true] 2 local3 n ([true]) ([false,false,true,true,true,true,true,false,true,true,true] ++ R)

theorem phase4 (n : Nat) (R : List Bool) : run0 table 21 ⟨0,[true,true,true,true],rep [true,true] n ++ [false,false,true,true,true,true,true,false,true,true,true] ++ R⟩ = some ⟨1,[false,true],[false,true,true,true,true] ++ rep [true,true] n ++ [false,false,true,true,true,true,true,false,true,true,true] ++ R⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 8 ⟨1,[false] ++ L,[false,true,true,true,true] ++ [true,true] ++ R⟩ = some ⟨1,[false] ++ [true,true] ++ L,[false,true,true,true,true] ++ R⟩ := by rfl

theorem phase5 (n : Nat) (R : List Bool) : run0 table (8*n) ⟨1,[false,true],[false,true,true,true,true] ++ rep [true,true] n ++ [false,false,true,true,true,true,true,false,true,true,true] ++ R⟩ = some ⟨1,[false] ++ rep [true,true] n ++ [true],[false,true,true,true,true,false,false,true,true,true,true,true,false,true,true,true] ++ R⟩ := by
  simpa only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using sweepR table 1 [false] [false,true,true,true,true] [true,true] [true,true] 8 local5 n ([true]) ([false,false,true,true,true,true,true,false,true,true,true] ++ R)

theorem phase6 (n : Nat) (R : List Bool) : run0 table 25 ⟨1,[false] ++ rep [true,true] n ++ [true],[false,true,true,true,true,false,false,true,true,true,true,true,false,true,true,true] ++ R⟩ = some ⟨0,[true,true,true,true] ++ rep [true,true] n ++ [true],[false,false,true,false,true,true,true,true,true,false,true,true,true] ++ R⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 2 ⟨0,[true,true,true,true] ++ [true,true] ++ L,R⟩ = some ⟨0,[true,true,true,true] ++ L,[true,true] ++ R⟩ := by rfl

theorem phase7 (n : Nat) (R : List Bool) : run0 table (2*n) ⟨0,[true,true,true,true] ++ rep [true,true] n ++ [true],[false,false,true,false,true,true,true,true,true,false,true,true,true] ++ R⟩ = some ⟨0,[true,true,true,true,true],rep [true,true] n ++ [false,false,true,false,true,true,true,true,true,false,true,true,true] ++ R⟩ := by
  simpa only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using sweepL table 0 [true,true,true,true] [] [true,true] [true,true] 2 local7 n ([true]) ([false,false,true,false,true,true,true,true,true,false,true,true,true] ++ R)

theorem phase8 (n : Nat) (R : List Bool) : run0 table 22 ⟨0,[true,true,true,true,true],rep [true,true] n ++ [false,false,true,false,true,true,true,true,true,false,true,true,true] ++ R⟩ = some ⟨1,[false,true],[false,true,true,true,true,true] ++ rep [true,true] n ++ [false,false,true,false,true,true,true,true,true,false,true,true,true] ++ R⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 8 ⟨1,[false] ++ L,[false,true,true,true,true,true] ++ [true,true] ++ R⟩ = some ⟨1,[false] ++ [true,true] ++ L,[false,true,true,true,true,true] ++ R⟩ := by rfl

theorem phase9 (n : Nat) (R : List Bool) : run0 table (8*n) ⟨1,[false,true],[false,true,true,true,true,true] ++ rep [true,true] n ++ [false,false,true,false,true,true,true,true,true,false,true,true,true] ++ R⟩ = some ⟨1,[false] ++ rep [true,true] n ++ [true],[false,true,true,true,true,true,false,false,true,false,true,true,true,true,true,false,true,true,true] ++ R⟩ := by
  simpa only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using sweepR table 1 [false] [false,true,true,true,true,true] [true,true] [true,true] 8 local9 n ([true]) ([false,false,true,false,true,true,true,true,true,false,true,true,true] ++ R)

theorem phase10 (n : Nat) (R : List Bool) : run0 table 73 ⟨1,[false] ++ rep [true,true] n ++ [true],[false,true,true,true,true,true,false,false,true,false,true,true,true,true,true,false,true,true,true] ++ R⟩ = some ⟨0,[true,true,true,true,true,true] ++ rep [true,true] n ++ [true],[false,false,false,false,false,false,true,true,true,false,false,false,false,true] ++ R⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 2 ⟨0,[true,true,true,true,true,true] ++ [true,true] ++ L,R⟩ = some ⟨0,[true,true,true,true,true,true] ++ L,[true,true] ++ R⟩ := by rfl

theorem phase11 (n : Nat) (R : List Bool) : run0 table (2*n) ⟨0,[true,true,true,true,true,true] ++ rep [true,true] n ++ [true],[false,false,false,false,false,false,true,true,true,false,false,false,false,true] ++ R⟩ = some ⟨0,[true,true,true,true,true,true,true],rep [true,true] n ++ [false,false,false,false,false,false,true,true,true,false,false,false,false,true] ++ R⟩ := by
  simpa only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using sweepL table 0 [true,true,true,true,true,true] [] [true,true] [true,true] 2 local11 n ([true]) ([false,false,false,false,false,false,true,true,true,false,false,false,false,true] ++ R)

theorem phase12 (n : Nat) (R : List Bool) : run0 table 7 ⟨0,[true,true,true,true,true,true,true],rep [true,true] n ++ [false,false,false,false,false,false,true,true,true,false,false,false,false,true] ++ R⟩ = some ⟨0,[],[true,true,true,true,true,true,true] ++ rep [true,true] n ++ [false,false,false,false,false,false,true,true,true,false,false,false,false,true] ++ R⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) (R : List Bool) : [true,true,true,true,true,true,true] ++ rep [true,true] n ++ [false,false,false,false,false,false,true,true,true,false,false,false,false,true] ++ R = [true,true,true,true,true,true] ++ rep [true,true] n ++ [true,false,false,false,false,false,false,true,true,true,false,false,false,false,true] ++ R := by
  calc
    _ = [true,true,true,true,true,true] ++ rep [true,true] n ++ [true,false,false,false,false,false,false,true,true,true,false,false,false,false,true] ++ R := by simpa only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using moveCut ([true,true,true,true,true,true]) ([false,false,false,false,false,false,true,true,true,false,false,false,false,true] ++ R) [true] true n

theorem epoch (n : Nat) (R : List Bool) : run0 table (211+30*n) (sect n R) = some (sect (n+2) ([false,false,false,false,true] ++ R)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R)) (phase4 n R)) (phase5 n R)) (phase6 n R)) (phase7 n R)) (phase8 n R)) (phase9 n R)) (phase10 n R)) (phase11 n R)) (phase12 n R))
  rw [finalR n R] at H
  rw [show 17+8*n+46+2*n+21+8*n+25+2*n+22+8*n+73+2*n+7=211+30*n by omega] at H
  simpa only [sect,rep,List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using H

abbrev W : List Bool := [false,false,false,false,true]

abbrev T : List Bool := [false,false,false,false,false,false,true,true,true,true,true]

def family (k : Nat) : Z0 := sect (2*k+4) (rep W k ++ T)

theorem entry : run0 table 510 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (k : Nat) : run0 table (331+60*k) (family k) = some (family (k+1)) := by
  have H := epoch (2*k+4) (rep W k ++ T)
  rw [show 211+30*(2*k+4)=331+60*k by omega] at H
  simpa only [family,show 2*(k+1)+4=(2*k+4)+2 by omega,rep,List.append_assoc] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 510 (fun k => 331+60*k) entry (by intro k; omega) growth m hm

#print axioms epoch
#print axioms entry
#print axioms growth
#print axioms never

end BB6.Agent10Raw108RC43
