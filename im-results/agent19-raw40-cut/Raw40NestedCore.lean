import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.NestedCore
open BB6Coverage BB6Coverage.Agent31Pump

/-- The shared six-entry core of Raw40 with A1=1RC and C1=0RC.
The B1/E/F entries are entirely unconstrained. -/
structure Core (p : PartialMachine) : Prop where
  a0 : p (0,false) = some (some ⟨true,true,1⟩)
  a1 : p (0,true) = some (some ⟨true,true,2⟩)
  c0 : p (2,false) = some (some ⟨false,true,3⟩)
  c1 : p (2,true) = some (some ⟨false,true,2⟩)
  d0 : p (3,false) = some (some ⟨true,false,3⟩)
  d1 : p (3,true) = some (some ⟨true,false,0⟩)

def zeros (n : Nat) := rep [false] n
def ones (n : Nat) := rep [true] n

theorem leftSweep (p : PartialMachine) (h : Core p) (a : Nat) (L R : List Bool) :
    run0 p a ⟨3,zeros a ++ L,R⟩ = some ⟨3,L,ones a ++ R⟩ := by
  have one (L R : List Bool) : run0 p 1 ⟨3,[false]++L,R⟩ = some ⟨3,L,[true]++R⟩ := by
    simp [run0,step0,move0,h.d0]
  simpa [zeros,ones] using sweepL p 3 [] [] [false] [true] 1 one a L R

theorem rightSweep (p : PartialMachine) (h : Core p) (a : Nat) (L R : List Bool) :
    run0 p a ⟨2,true::L,ones a ++ R⟩ = some ⟨2,true::(zeros a ++ L),R⟩ := by
  have one (L R : List Bool) : run0 p 1 ⟨2,[true]++L,[true]++R⟩ = some ⟨2,[true]++[false]++L,R⟩ := by
    simp [run0,step0,move0,h.c1]
  simpa [zeros,ones] using sweepR p 2 [true] [] [true] [false] 1 one a L R

/-- One inner epoch: consume one of at least two remaining ones, append three
zeros, and return to D at the right edge. -/
theorem epoch (p : PartialMachine) (h : Core p) (a : Nat) (L : List Bool) :
    run0 p (2*a+4) ⟨3,zeros a ++ true::true::L,[]⟩ =
      some ⟨3,zeros (a+3) ++ true::L,[]⟩ := by
  have h1 : run0 p a ⟨3,zeros a ++ true::true::L,[]⟩ = some ⟨3,true::true::L,ones a⟩ := by
    simpa only [List.append_nil] using leftSweep p h a (true::true::L) []
  have h2 : run0 p 2 ⟨3,true::true::L,ones a⟩ = some ⟨2,true::true::L,ones a⟩ := by
    simp [run0,step0,move0,h.d1,h.a1]
  have h3 := rightSweep p h a (true::L) []
  simp only [List.append_nil] at h3
  have h4 : run0 p 2 ⟨2,true::(zeros a ++ true::L),[]⟩ =
      some ⟨3,zeros (a+3) ++ true::L,[]⟩ := by
    simp [run0,step0,move0,h.c1,h.c0,zeros,rep]
  have H := join0 (join0 (join0 h1 h2) h3) h4
  rwa [show a+2+a+2=2*a+4 by omega] at H

/-- Final epoch when only one marker remains. -/
theorem finish (p : PartialMachine) (h : Core p) (a : Nat) :
    run0 p (a+2) ⟨3,zeros a ++ [true],[]⟩ = some ⟨1,[true,true],ones a⟩ := by
  have h1 : run0 p a ⟨3,zeros a ++ [true],[]⟩ = some ⟨3,[true],ones a⟩ := by
    simpa only [List.append_nil] using leftSweep p h a [true] []
  have h2 : run0 p 2 ⟨3,[true],ones a⟩ = some ⟨1,[true,true],ones a⟩ := by
    simp [run0,step0,move0,h.d1,h.a0]
  exact join0 h1 h2

def cost (a : Nat) : Nat → Nat
  | 0 => a+2
  | k+1 => (2*a+4)+cost (a+3) k

theorem cost_pos (a k : Nat) : 0 < cost a k := by
  cases k <;> simp [cost] <;> omega

/-- Nested sweep, valid for every choice of the other six entries. -/
theorem collapse (p : PartialMachine) (h : Core p) (a k : Nat) :
    run0 p (cost a k) ⟨3,zeros a ++ ones (k+1),[]⟩ =
      some ⟨1,[true,true],ones (a+3*k)⟩ := by
  induction k generalizing a with
  | zero => simpa [cost,ones,rep] using finish p h a
  | succ k ih =>
    have h1 := epoch p h a (ones k)
    have h2 := ih (a+3)
    have H := join0 h1 h2
    simpa only [cost,ones,rep,List.singleton_append,show a+3+3*k=a+3*(k+1) by omega] using H

/-- The B-side frame records the completed unary transfers. -/
def frame (z : Nat) : List Bool := [true,true] ++ zeros z ++ [true]

/-- Finite boundary checks suffice for the entire nested counter. -/
structure Boundary (p : PartialMachine) (z t u : Nat) : Prop where
  first : ∀ R, run0 p t ⟨1,[true,true],true::R⟩ = some ⟨1,frame z,R⟩
  transfer : ∀ L R, run0 p t ⟨1,frame z ++ L,true::R⟩ =
      some ⟨1,frame z ++ true::L,R⟩
  turn : ∀ L, run0 p u ⟨1,frame z ++ L,[]⟩ =
      some ⟨3,zeros (z+2) ++ true::true::L,[]⟩

def outerFamily (n : Nat) : Z0 := ⟨1,[true,true],ones (n+1)⟩
def outerCost (z t u n : Nat) : Nat := t + t*n + u + cost (z+2) (n+1)

theorem outer (p : PartialMachine) (h : Core p) (z t u : Nat) (b : Boundary p z t u) (n : Nat) :
    run0 p (outerCost z t u n) (outerFamily n) = some (outerFamily (3*n+z+4)) := by
  have h1 := b.first (ones n)
  have one (L R : List Bool) : run0 p t ⟨1,frame z++L,[]++[true]++R⟩ =
      some ⟨1,frame z++[true]++L,[]++R⟩ := by simpa using b.transfer L R
  have h2 := sweepR p 1 (frame z) [] [true] [true] t one n [] []
  simp only [List.nil_append,List.append_nil] at h2
  have h3 := b.turn (ones n)
  have h4 := collapse p h (z+2) (n+1)
  have H := join0 (join0 (join0 h1 h2) h3) h4
  simpa only [outerCost,outerFamily,ones,rep,List.singleton_append,
    show z+2+3*(n+1)=3*n+z+4+1 by omega] using H

def index (z initial : Nat) : Nat → Nat
  | 0 => initial
  | n+1 => 3*index z initial n+z+4

theorem never (p : PartialMachine) (h : Core p) (z t u : Nat) (b : Boundary p z t u)
    (entry initial : Nat) (first : run0 p entry ⟨0,[],[]⟩ = some (outerFamily initial))
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun n => outerFamily (index z initial n)) entry
    (fun n => outerCost z t u (index z initial n)) _ _ _ m hm
  · exact first
  · intro n
    have hp := cost_pos (z+2) (index z initial n+1)
    unfold outerCost
    omega
  · intro n
    exact outer p h z t u b (index z initial n)

#print axioms collapse
#print axioms outer
#print axioms never
end BB6.Agent19Raw40.NestedCore
