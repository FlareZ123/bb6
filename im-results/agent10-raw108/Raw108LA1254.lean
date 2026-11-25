import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw108LA1254
open BB6Coverage BB6Coverage.Agent31Pump
def table : PartialMachine := fun s =>
  match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨true,false,5⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,false,0⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨true,true,2⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,4⟩)
  | (4,true) => some (some ⟨true,false,1⟩)
  | (5,false) => some (some ⟨true,true,2⟩)
  | (5,true) => some (some ⟨true,false,0⟩)
  | _ => none
abbrev P : List Bool := [true,true,true,true]
abbrev a : List Bool := [true,true,false,true,true]
abbrev b : List Bool := [false,true,true]
def family (n : Nat) : Z0 := ⟨4,a++rep P n,[]⟩
theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem first (L : List Bool) : run0 table 11 ⟨4,a++L,[]⟩ = some ⟨0,P++L,b⟩ := by rfl
theorem left_one (L R : List Bool) : run0 table 4 ⟨0,P++L,R⟩ = some ⟨0,L,P++R⟩ := by rfl
theorem middle (R : List Bool) : run0 table 11 ⟨0,[],P++R⟩ = some ⟨2,true::P,true::R⟩ := by rfl
theorem right_one (L R : List Bool) : run0 table 4 ⟨2,true::L,true::(P++R)⟩ = some ⟨2,true::(P++L),true::R⟩ := by rfl
theorem final (L : List Bool) : run0 table 4 ⟨2,true::L,true::b⟩ = some ⟨4,a++L,[]⟩ := by rfl
theorem growth (n : Nat) : run0 table (30+8*n) (family n) = some (family (n+1)) := by
  have h1 := first (rep P n)
  have h2 := sweepL table 0 [] [] P P 4 left_one (n+1) [] b
  have h3 := middle (rep P n++b)
  have h4 := sweepR table 2 [true] [true] P P 4 right_one n P b
  have h5 := final (rep P n++P)
  have H := join0 (join0 (join0 (join0 h1 (by simpa only [rep,List.nil_append,List.append_nil,List.append_assoc] using h2)) (by simpa only [rep,List.append_assoc] using h3)) (by simpa only [List.cons_append,List.nil_append,List.append_assoc] using h4)) h5
  rw [show 11+4*(n+1)+11+4*n+4=30+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,rep_snoc] using H
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 30+8*n) entry (by intro n; omega) growth m hm
#print axioms never
end BB6.Agent10Raw108LA1254
