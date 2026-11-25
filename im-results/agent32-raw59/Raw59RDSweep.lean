import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw59RD
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none
abbrev O (n : Nat) := rep [true,true,true,true] n

def family (n : Nat) : Z0 := ⟨1,[],[false,true,false]++O (n+1)⟩

theorem entry : run0 table 23 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem enter (R : List Bool) : run0 table 7 ⟨1,[],[false,true,false]++R⟩ = some ⟨4,[true,true,false,true],R⟩ := by rfl

theorem rightSweep (k : Nat) : run0 table (12*k) ⟨4,[true,true,false,true],O k⟩ = some ⟨4,[true,true]++O k++[false,true],[]⟩ := by
  simpa only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using sweepR table 4 [true,true] [] [true,true,true,true] [true,true,true,true] 12 (by intro L R; rfl) k [false,true] []

theorem turn (W : List Bool) : run0 table 3 ⟨4,[true,true]++W,[]⟩ = some ⟨4,[false,true,true]++W,[]⟩ := by rfl

theorem leftSweep (k : Nat) : run0 table (12*k) ⟨4,[false,true,true]++O k++[false,true],[]⟩ = some ⟨4,[false,true,true,false,true],O k⟩ := by
  simpa only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using sweepL table 4 [false,true,true] [] [true,true,true,true] [true,true,true,true] 12 (by intro L R; rfl) k [false,true] []

theorem leave (R : List Bool) : run0 table 15 ⟨4,[false,true,true,false,true],R⟩ = some ⟨1,[],[false,true,false,true,true,true,true]++R⟩ := by rfl

def epoch (n : Nat) := 49+24*n

theorem growth (n : Nat) : run0 table (epoch n) (family n) = some (family (n+1)) := by
  have h1 := enter (O (n+1))
  have h2 := rightSweep (n+1)
  have h3 := turn (O (n+1)++[false,true])
  rw [← List.append_assoc] at h3
  have h4 := leftSweep (n+1)
  have h5 := leave (O (n+1))
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [show 7+12*(n+1)+3+12*(n+1)+15=epoch n by unfold epoch; omega] at h
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 23 epoch entry (by intro n; unfold epoch; omega) growth m hm
#print axioms growth
#print axioms never
end BB6.Agent32Raw59RD
