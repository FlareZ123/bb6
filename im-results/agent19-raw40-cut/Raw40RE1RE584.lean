
import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.RE1RE584
open BB6Coverage BB6Coverage.Agent31Pump

-- 1RB1RE_1RC0RF_0RD1RB_1LD1LA_1LF1RE_---0LA
-- All 25 F0 completions are nonhalting.
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def U : List Bool := [true,true,true]
def family (n : Nat) : Z0 := ⟨0,[true]++rep U (3*n),U⟩
theorem entry : run0 table 6 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem start (L : List Bool) :
    run0 table 6 ⟨0,true::L,U⟩ =
      some ⟨0,U++L,[false,true]⟩ := by rfl

theorem leftTriple (L R : List Bool) :
    run0 table 9 ⟨0,U++L,[false]++R⟩ =
      some ⟨0,L,[false]++U++R⟩ := by rfl

theorem leftPair (L R : List Bool) :
    run0 table 6 ⟨0,[true,true]++L,[false]++R⟩ =
      some ⟨0,L,[false,true,true]++R⟩ := by rfl

theorem firstRight (R : List Bool) :
    run0 table 5 ⟨0,[],[false]++U++R⟩ =
      some ⟨0,[false]++U,[false]++R⟩ := by rfl

theorem rightOne (L R : List Bool) :
    run0 table 5 ⟨0,[false]++L,[false]++U++R⟩ =
      some ⟨0,[false]++U++L,[false]++R⟩ := by rfl

theorem turn8 (L : List Bool) :
    run0 table 8 ⟨0,[false]++U++L,[false,true]⟩ =
      some ⟨0,U++U++L,U⟩ := by rfl

theorem turn6 (L : List Bool) :
    run0 table 6 ⟨0,[false]++U++L,[false]⟩ =
      some ⟨0,[true]++U++L,U⟩ := by rfl

theorem leftSweep (k : Nat) (R : List Bool) :
    run0 table (9*k) ⟨0,rep U k,[false]++R⟩ =
      some ⟨0,[],[false]++rep U k++R⟩ := by
  have H := sweepL table 0 [] [false] U U 9 leftTriple k [] R
  simpa only [List.nil_append,List.append_nil,List.append_assoc] using H

theorem rightSweep (k : Nat) (R : List Bool) :
    run0 table (5*k) ⟨0,[false]++U,[false]++rep U k++R⟩ =
      some ⟨0,[false]++rep U (k+1),[false]++R⟩ := by
  have H := sweepR table 0 [false] [false] U U 5 rightOne k U R
  simp only [List.append_assoc] at H ⊢
  rw [rep_snoc] at H
  exact H

theorem phaseA (k : Nat) :
    run0 table (14*k+28) ⟨0,[true]++rep U k,U⟩ =
      some ⟨0,rep U (k+2),U⟩ := by
  have h1 := start (rep U k)
  have h2 := leftSweep (k+1) [true]
  have h3 := firstRight (rep U k++[true])
  have h4 := rightSweep k [true]
  have h5 := turn8 (rep U k)
  have h3' : run0 table 5 ⟨0,[],[false]++rep U (k+1)++[true]⟩ =
      some ⟨0,[false]++U,[false]++rep U k++[true]⟩ := by
    simpa only [rep,List.append_assoc] using h3
  have H := join0 (join0 (join0 (join0 h1 h2) h3') h4) h5
  rw [show 6+9*(k+1)+5+5*k+8=14*k+28 by omega] at H
  simpa only [rep,List.append_assoc,List.singleton_append] using H

theorem phaseB (k : Nat) :
    run0 table (14*k+51) ⟨0,rep U (k+2),U⟩ =
      some ⟨0,[true]++rep U (k+3),U⟩ := by
  have h1 := start ([true,true]++rep U (k+1))
  have h1' : run0 table 6 ⟨0,rep U (k+2),U⟩ =
      some ⟨0,[true,true]++rep U (k+2),[false,true]⟩ := by
    simpa only [rep,U,List.append_assoc,List.cons_append,List.nil_append] using h1
  have h2 := leftPair (rep U (k+2)) [true]
  have h3 := leftSweep (k+2) U
  have h3' : run0 table (9*(k+2)) ⟨0,rep U (k+2),[false]++U⟩ =
      some ⟨0,[],[false]++rep U (k+3)⟩ := by
    have eq : rep U (k+2)++U = rep U (k+3) := by rw [rep_snoc]; rfl
    rw [List.append_assoc,eq] at h3
    exact h3
  have h4 := firstRight (rep U (k+2))
  have h5 := rightSweep (k+2) []
  simp only [List.append_nil] at h5
  have h6 := turn6 (rep U (k+2))
  have H := join0 (join0 (join0 (join0 (join0 h1' h2) h3') h4) h5) h6
  rw [show 6+6+9*(k+2)+5+5*(k+2)+6=14*k+51 by omega] at H
  simpa only [rep,List.append_assoc] using H

theorem growth (n : Nat) :
    run0 table (84*n+79) (family n) = some (family (n+1)) := by
  have H := join0 (phaseA (3*n)) (phaseB (3*n))
  rw [show 14*(3*n)+28+(14*(3*n)+51)=84*n+79 by omega] at H
  simpa only [family,show 3*n+3=3*(n+1) by omega] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 6 (fun n => 84*n+79) entry (by omega) growth m hm
#print axioms never
end BB6.Agent19Raw40.RE1RE584
