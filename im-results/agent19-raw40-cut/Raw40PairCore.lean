import Raw40NestedCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.PairCore
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent19Raw40.NestedCore

private theorem onesAdd (a b : Nat) : ones (a+b) = ones a ++ ones b := by
  induction a with
  | zero => simp [ones,rep]
  | succ a ih =>
    rw [show a+1+b=(a+b)+1 by omega]
    change [true] ++ ones (a+b) = ([true] ++ ones a) ++ ones b
    rw [ih,List.append_assoc]
private theorem pair (n : Nat) : rep [true,true] n = ones (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,ih,show 2*(n+1)=2+2*n by omega,onesAdd]; rfl

def frame2 (z : Nat) : List Bool := [true,true] ++ zeros (2*z) ++ [true,true]
structure Boundary2 (p : PartialMachine) (z t u : Nat) : Prop where
  first : ∀ R, run0 p t ⟨1,[true,true],[true,true]++R⟩ = some ⟨1,frame2 z,R⟩
  transfer : ∀ L R, run0 p t ⟨1,frame2 z++L,[true,true]++R⟩ =
      some ⟨1,frame2 z++[true,true]++L,R⟩
  turn : ∀ L, run0 p u ⟨1,frame2 z++L,[true]⟩ =
      some ⟨3,zeros (2*z+2)++[true,true,true,true]++L,[]⟩

def family2 (n : Nat) : Z0 := ⟨1,[true,true],ones (2*n+3)⟩
def cost2 (z t u n : Nat) := t+t*n+u+cost (2*z+2) (2*n+3)

theorem outer2 (p : PartialMachine) (h : Core p) (z t u : Nat) (b : Boundary2 p z t u) (n : Nat) :
    run0 p (cost2 z t u n) (family2 n) = some (family2 (3*n+z+4)) := by
  have h1 := b.first (rep [true,true] n++[true])
  have h1' : run0 p t (family2 n) = some ⟨1,frame2 z,rep [true,true] n++[true]⟩ := by
    unfold family2
    rw [show 2*n+3=2+(2*n+1) by omega,onesAdd,onesAdd,pair] at *
    exact h1
  have one (L R : List Bool) : run0 p t ⟨1,frame2 z++L,[]++[true,true]++R⟩ =
      some ⟨1,frame2 z++[true,true]++L,[]++R⟩ := by simpa using b.transfer L R
  have h2 := sweepR p 1 (frame2 z) [] [true,true] [true,true] t one n [] [true]
  simp only [List.nil_append,List.append_nil] at h2
  have h3 := b.turn (rep [true,true] n)
  have h4 := collapse p h (2*z+2) (2*n+3)
  have h3' : run0 p u ⟨1,frame2 z++rep [true,true] n,[true]⟩ =
      some ⟨3,zeros (2*z+2)++ones (2*n+3+1),[]⟩ := by
    rw [show 2*n+3+1=4+2*n by omega,onesAdd,← pair]
    simpa only [show ones 4 = [true,true,true,true] by rfl,List.append_assoc] using h3
  have H := join0 (join0 (join0 h1' h2) h3') h4
  simpa only [cost2,family2,show 2*z+2+3*(2*n+3)=2*(3*n+z+4)+3 by omega] using H

theorem never2 (p : PartialMachine) (h : Core p) (z t u : Nat) (b : Boundary2 p z t u)
    (entry initial : Nat) (first : run0 p entry ⟨0,[],[]⟩ = some (family2 initial))
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun n => family2 (index z initial n)) entry
    (fun n => cost2 z t u (index z initial n)) _ _ _ m hm
  · exact first
  · intro n
    have hp := cost_pos (2*z+2) (2*index z initial n+3)
    unfold cost2
    omega
  · intro n
    exact outer2 p h z t u b (index z initial n)
#print axioms outer2
#print axioms never2
end BB6.Agent19Raw40.PairCore
