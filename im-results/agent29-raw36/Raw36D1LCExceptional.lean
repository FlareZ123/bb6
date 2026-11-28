import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29Raw36D1LCExceptional
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨false,false,3⟩)
  | 3,true => some (some ⟨false,false,2⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

abbrev X : List Bool := [true,false,true,false]
abbrev Y : List Bool := [false,true,false,true]
def family (n : Nat) : Z0 := ⟨0,[],[false] ++ rep X n ++ [true,false,true,false,false]⟩
theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem h0 (n : Nat) : run0 table 1 (family n) = some ⟨1,[false,true],rep X n ++ [true,false,true,false,false]⟩ := by rfl

theorem oneR (L R : List Bool) : run0 table 10 ⟨1,[false] ++ L, X ++ R⟩ = some ⟨1,[false] ++ X ++ L,R⟩ := by rfl

theorem h1 (n : Nat) : run0 table (10*n) ⟨1,[false,true],rep X n ++ [true,false,true,false,false]⟩ =
    some ⟨1,[false] ++ rep X n ++ [true],[true,false,true,false,false]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using
    sweepR table 1 [false] [] X X 10 oneR n [true] [true,false,true,false,false]

theorem h2 (n : Nat) : run0 table 16 ⟨1,[false] ++ rep X n ++ [true],[true,false,true,false,false]⟩ =
    some ⟨4,[false,true,false,true,false] ++ rep X n ++ [true],[false,false]⟩ := by rfl

theorem oneL (L R : List Bool) : run0 table 4 ⟨4,[false,true,false,true,false] ++ X ++ L,R⟩ =
    some ⟨4,[false,true,false,true,false] ++ L,Y ++ R⟩ := by rfl

theorem h3 (n : Nat) : run0 table (4*n) ⟨4,[false,true,false,true,false] ++ rep X n ++ [true],[false,false]⟩ =
    some ⟨4,[false,true,false,true,false,true],rep Y n ++ [false,false]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using
    sweepL table 4 [false,true,false,true,false] [] X Y 4 oneL n [true] [false,false]

theorem h4 (n : Nat) : run0 table 8 ⟨4,[false,true,false,true,false,true],rep Y n ++ [false,false]⟩ =
    some ⟨0,[],[false,true,false,true,false,true,false,true] ++ rep Y n ++ [false,false]⟩ := by rfl

theorem commute (n : Nat) : [true,false,true] ++ rep Y n = rep X n ++ [true,false,true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,List.append_assoc]
    change X ++ ([true,false,true] ++ rep Y n) = X ++ (rep X n ++ [true,false,true])
    rw [ih]

theorem endEq (n : Nat) : (⟨0,[],[false,true,false,true,false,true,false,true] ++ rep Y n ++ [false,false]⟩ : Z0) = family (n+1) := by
  unfold family
  simp only [rep,List.append_assoc]
  change (⟨0,[],[false,true,false,true,false] ++ ([true,false,true] ++ rep Y n) ++ [false,false]⟩ : Z0) = _
  rw [commute]
  simp only [List.append_assoc]
  rfl

theorem growth (n : Nat) : run0 table (14*n+25) (family n) = some (family (n+1)) := by
  have h := join0 (h0 n) (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  rw [endEq] at h
  rw [show 14*n+25 = 1+10*n+16+4*n+8 by omega]
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 (fun n => 14*n+25) entry (by intro n; omega) growth m hm
#print axioms growth
#print axioms never
end BB6.Agent29Raw36D1LCExceptional
