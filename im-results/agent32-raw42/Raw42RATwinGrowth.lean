import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw42RA.TwinGrowth
open BB6Coverage BB6Coverage.Agent31Pump

def table (alt : Bool) : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨true,true,4⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,true,0⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => if alt then none else some (some ⟨false,false,5⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨false,false,1⟩)
  | (4,false) => some (some ⟨true,false,if alt then 5 else 2⟩)
  | (4,true) => some (some ⟨true,true,0⟩)
  | (5,false) => some (some ⟨false,false,3⟩)
  | (5,true) => if alt then some (some ⟨false,false,5⟩) else none
  | _ => none

def A : List Bool := [true,true]
def B : List Bool := [true,false,true]
def family (n : Nat) : Z0 := ⟨0,[false,true,true] ++ rep A n ++ [false,true,false,true] ++ rep B n,[]⟩

theorem entry (alt : Bool) : run0 (table alt) 35 ⟨0,[],[]⟩ = some (family 0) := by cases alt <;> decide

theorem startPhase (alt : Bool) (L : List Bool) :
    run0 (table alt) 10 ⟨0,[false,true,true]++L,[]⟩ =
      some ⟨4,[false,true,false,true,false,true,true]++L,[]⟩ := by cases alt <;> rfl

theorem leftTransfer (alt : Bool) (L R : List Bool) :
    run0 (table alt) 26 ⟨4,[false,true,false,true,false,true,true]++A++L,R⟩ =
      some ⟨4,[false,true,false,true,false,true,true]++L,A++R⟩ := by cases alt <;> rfl

theorem middlePhase (alt : Bool) (L R : List Bool) :
    run0 (table alt) 49 ⟨4,[false,true,false,true,false,true,true,false,true,false,true]++L,R⟩ =
      some ⟨0,[true,false,true,false,true,true,false,true]++L,[true,true,true]++R⟩ := by cases alt <;> rfl

theorem rightTransfer (alt : Bool) (L R : List Bool) :
    run0 (table alt) 2 ⟨0,[true]++L,[true,true,true]++A++R⟩ =
      some ⟨0,[true]++A++L,[true,true,true]++R⟩ := by cases alt <;> rfl

theorem finishPhase (alt : Bool) (L : List Bool) :
    run0 (table alt) 4 ⟨0,[true]++L,[true,true,true]⟩ =
      some ⟨0,[false,true,true,true,true]++L,[]⟩ := by cases alt <;> rfl

theorem grow (alt : Bool) (n : Nat) : run0 (table alt) (63+28*n) (family n) = some (family (n+1)) := by
  have h0 := startPhase alt (rep A n ++ [false,true,false,true] ++ rep B n)
  have h1 := sweepL (table alt) 4 [false,true,false,true,false,true,true] [] A A 26 (leftTransfer alt) n ([false,true,false,true]++rep B n) []
  have h2 := middlePhase alt (rep B n) (rep A n)
  have h3 := sweepR (table alt) 0 [true] [true,true,true] A A 2 (rightTransfer alt) n ([false,true,false,true,true,false,true]++rep B n) []
  have h4 := finishPhase alt (rep A n ++ [false,true,false,true,true,false,true]++rep B n)
  simp only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h0 h1 h2 h3 h4
  have h := join0 (join0 (join0 (join0 h0 h1) h2) h3) h4
  rw [show 10+26*n+49+2*n+4 = 63+28*n by omega] at h
  simpa only [family,rep,A,B,List.append_assoc,List.cons_append,List.nil_append] using h

theorem never (alt : Bool) : ∀ m, compatible (table alt) m → NeverHalts m :=
  never_of_growth (table alt) family 35 (fun n => 63+28*n) (entry alt) (by omega) (grow alt)
#print axioms never
end BB6.Agent32Raw42RA.TwinGrowth
