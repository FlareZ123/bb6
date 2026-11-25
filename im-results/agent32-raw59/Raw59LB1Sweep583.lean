import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw59LB1Sweep583
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | _,_ => none

abbrev X := [false,true,false,true]
abbrev Y := [false,false,true,true]
abbrev O (n : Nat) := rep [true] n
abbrev P := [true,false]
abbrev Q := [true,true]
abbrev S := [true]

def family (n : Nat) : Z0 := ⟨4,O (n+4),S++rep Y (n+1)⟩

theorem entry : run0 table 35 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem start (L R : List Bool) :
    run0 table 9 ⟨4,[true,true,true]++L,S++R⟩ =
      some ⟨4,[true,false,true,true]++L,R⟩ := by rfl

theorem right (n : Nat) (L R : List Bool) :
    run0 table (6*n) ⟨4,P++L,rep Y n++R⟩ =
      some ⟨4,P++rep X n++L,R⟩ := by
  simpa only [List.nil_append] using sweepR table 4 P [] Y X 6 (by intro L R; rfl) n L R

theorem turn (L : List Bool) :
    run0 table 10 ⟨4,P++L,[]⟩ = some ⟨4,Q++X++L,S⟩ := by rfl

theorem left (n : Nat) (L R : List Bool) :
    run0 table (10*n) ⟨4,Q++rep X n++L,S++R⟩ =
      some ⟨4,Q++L,S++rep Y n++R⟩ := by
  exact sweepL table 4 Q S X Y 10 (by intro L R; rfl) n L R

def epoch (n : Nat) := 9+6*(n+1)+10+10*(n+2)

theorem growth (n : Nat) : run0 table (epoch n) (family n) = some (family (n+1)) := by
  have h1 : run0 table 9 (family n) = some ⟨4,P++O (n+3),rep Y (n+1)⟩ := by
    exact start (O (n+1)) (rep Y (n+1))
  have h2 := right (n+1) (O (n+3)) []
  simp only [List.append_nil] at h2
  have h3 : run0 table 10 ⟨4,P++rep X (n+1)++O (n+3),[]⟩ =
      some ⟨4,Q++rep X (n+2)++O (n+3),S⟩ := by
    simpa only [rep,List.append_assoc] using turn (rep X (n+1)++O (n+3))
  have h4 := left (n+2) (O (n+3)) []
  simp only [List.append_nil] at h4
  have H := join0 (join0 (join0 h1 h2) h3) h4
  exact H

theorem epoch_exact (n : Nat) : epoch n = 16*n+45 := by unfold epoch; omega

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 35 epoch entry (by intro n; unfold epoch; omega) growth m hm

#print axioms entry
#print axioms growth
#print axioms epoch_exact
#print axioms never
end BB6.Agent32Raw59LB1Sweep583
