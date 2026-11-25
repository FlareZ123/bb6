import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw59LBSweep583
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
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

abbrev X := [true,false,true,false]
abbrev Y := [false,false,true,true]
abbrev O (n : Nat) := rep [true] n
abbrev F := [false,false]
abbrev G := [false,true,true]

def family (n : Nat) : Z0 := ⟨4,F ++ rep X n ++ O (n+3),[]⟩

theorem entry : run0 table 18 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem extend (L : List Bool) :
    run0 table 4 ⟨4,F++L,[]⟩ = some ⟨3,F++X++L,[]⟩ := by rfl

theorem left (n : Nat) (L R : List Bool) :
    run0 table (10*n) ⟨3,F++rep X n++L,R⟩ =
      some ⟨3,F++L,rep Y n++R⟩ := by
  simpa only [List.nil_append] using sweepL table 3 F [] X Y 10 (by intro L R; rfl) n L R

theorem turn (L R : List Bool) :
    run0 table 15 ⟨3,F++[true,true]++L,Y++R⟩ =
      some ⟨4,F++[true,true,true]++L,G++R⟩ := by rfl

theorem right (n : Nat) (L R : List Bool) :
    run0 table (6*n) ⟨4,F++L,G++rep Y n++R⟩ =
      some ⟨4,F++rep X n++L,G++R⟩ := by
  exact sweepR table 4 F G Y X 6 (by intro L R; rfl) n L R

theorem finish (L : List Bool) :
    run0 table 6 ⟨4,F++L,G⟩ = some ⟨4,F++X++L,[]⟩ := by rfl

def epoch (n : Nat) := 4+10*(n+1)+15+6*n+6

theorem growth (n : Nat) : run0 table (epoch n) (family n) = some (family (n+1)) := by
  have h1 := extend (rep X n ++ O (n+3))
  have h2 := left (n+1) (O (n+3)) []
  have h3 := turn (O (n+1)) (rep Y n)
  have h4 := right n (O (n+4)) []
  have h5 := finish (rep X n ++ O (n+4))
  simp only [List.append_nil] at h2 h4
  have h12 : run0 table (4+10*(n+1)) (family n) =
      some ⟨3,F++O (n+3),rep Y (n+1)⟩ := by
    apply join0 (b := ⟨3,F++rep X (n+1)++O (n+3),[]⟩)
    · simpa only [family,rep,List.append_assoc] using h1
    · exact h2
  have h3' : run0 table 15 ⟨3,F++O (n+3),rep Y (n+1)⟩ =
      some ⟨4,F++O (n+4),G++rep Y n⟩ := by
    exact h3
  have h123 := join0 h12 h3'
  have h1234 := join0 h123 h4
  rw [List.append_assoc] at h1234
  have H := join0 h1234 h5
  simpa only [epoch,family,rep,List.append_assoc,Nat.add_assoc] using H

theorem epoch_exact (n : Nat) : epoch n = 16*n+35 := by unfold epoch; omega

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 18 epoch entry (by intro n; unfold epoch; omega) growth m hm
#print axioms growth
#print axioms epoch_exact
#print axioms never
end BB6.Agent32Raw59LBSweep583
