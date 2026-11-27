import SweepPumping

namespace BB6.Agent32Raw421LB.Leaf4828
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def p : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨false,true,5⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨true,false,1⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨false,true,4⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨false,false,1⟩)
  | (4,false) => some (some ⟨false,true,0⟩)
  | (4,true) => some (some ⟨false,false,3⟩)
  | (5,true) => some (some ⟨false,true,3⟩)
  | _ => none

def B (L R : List Bool) : Z0 := ⟨1,false::L,R⟩
def ones := rep [true]

theorem seed : run0 p 7 ⟨0,[],[]⟩ =
    some ⟨1,[],[true,false,true,true]⟩ := by decide

theorem transferOne (L R : List Bool) :
    run0 p 3 (B L (false::true::R)) = some (B (true::L) (false::R)) := by rfl

theorem sweepOne (L R : List Bool) :
    run0 p 1 ⟨1,true::L,R⟩ = some ⟨1,L,true::R⟩ := by rfl

theorem transferMany (b : Nat) (L R : List Bool) :
    run0 p (3*b) (B L (false::(ones b ++ R))) =
    some (B (ones b ++ L) (false::R)) := by
  have h := sweepR p 1 [false] [false] [true] [true] 3
    (by intro L R; rfl) b L R
  simpa only [B,ones,List.cons_append,List.nil_append,List.append_nil] using h

theorem sweepMany (k : Nat) (L R : List Bool) :
    run0 p k ⟨1,ones k ++ L,R⟩ = some ⟨1,L,ones k ++ R⟩ := by
  have h := sweepL p 1 [] [] [true] [true] 1
    (by intro L R; rfl) k L R
  simpa only [ones,Nat.one_mul,List.nil_append] using h

theorem turn00 (L R : List Bool) :
    run0 p 5 (B L ([false,false]++R)) = some ⟨1,L,[false,true,true]++R⟩ := by rfl

theorem turn11 (L R : List Bool) :
    run0 p 5 (B L ([true,true]++R)) = some ⟨1,L,[false,true,false]++R⟩ := by rfl

theorem turn1000 (L R : List Bool) :
    run0 p 4 (B L ([true,false,false,false]++R)) =
    some (B ([true,false,false,true]++L) R) := by rfl

theorem turn1001 (L R : List Bool) :
    run0 p 6 (B L ([true,false,false,true]++R)) =
    some (B ([false,true]++L) ([true,true]++R)) := by rfl

theorem terminal1010 (L R : List Bool) :
    run0 p 4 (B L ([true,false,true,false]++R)) =
    some ⟨5,[false,false,false,false,true]++L,R⟩ := by rfl

theorem hole1010 (L R : List Bool) :
    run0 p 5 (B L ([true,false,true,false]++R)) = none := by rfl

theorem turn10110 (L R : List Bool) :
    run0 p 11 (B L ([true,false,true,true,false]++R)) =
    some ⟨1,L,[false,true,true,true,true,true]++R⟩ := by rfl

theorem turn10111 (L R : List Bool) :
    run0 p 6 (B L ([true,false,true,true,true]++R)) =
    some (B ([false,false,false,true]++L) (false::R)) := by rfl

theorem ones_add (a b : Nat) : ones a ++ ones b = ones (a+b) := by
  induction a with
  | zero => simp [ones,rep]
  | succ a ih =>
    rw [show a+1+b=a+b+1 by omega]
    simp only [ones,rep,List.append_assoc,List.cons_append,List.nil_append] at ih ⊢
    rw [ih]

/-- General a=0 rule, with an explicit zero delimiter on the left.
    Right suffix R starts at the third run, and is otherwise arbitrary. -/
theorem macro0 (k b : Nat) (L R : List Bool) :
    run0 p (4*b+k+5) (B (ones k ++ false::L) (false::(ones b ++ false::R))) =
    some (B L (ones (b+k) ++ [false,true,true]++R)) := by
  have h0 := transferMany b (ones k ++ false::L) (false::R)
  have h1 := turn00 (ones b ++ (ones k ++ false::L)) R
  have h2 := sweepMany (b+k) (false::L) ([false,true,true]++R)
  rw [← ones_add b k] at h2
  have h1' : run0 p 5 (B (ones b ++ (ones k ++ false::L)) (false::false::R)) =
      some ⟨1,ones b ++ (ones k ++ false::L),[false,true,true]++R⟩ := h1
  have h2' : run0 p (b+k) ⟨1,ones b ++ (ones k ++ false::L),[false,true,true]++R⟩ =
      some (B L ((ones b ++ ones k) ++ [false,true,true]++R)) := by
    simpa only [B,List.append_assoc] using h2
  have h := join0 (join0 h0 h1') h2'
  rw [show 3*b+5+(b+k)=4*b+k+5 by omega, ones_add b k] at h
  simpa only [List.append_assoc] using h

/-- General a>=2 rule, with the first two ones exposed on the right. -/
theorem macroMany (k : Nat) (L R : List Bool) :
    run0 p (k+5) (B (ones k ++ false::L) ([true,true]++R)) =
    some (B L (ones k ++ [false,true,false]++R)) := by
  have h0 := turn11 (ones k ++ false::L) R
  have h1 := sweepMany k (false::L) ([false,true,false]++R)
  have h := join0 h0 h1
  rw [show 5+k=k+5 by omega] at h
  simpa only [B,List.append_assoc] using h

theorem macroTwo (k : Nat) (L R : List Bool) :
    run0 p (k+11) (B (ones k ++ false::L) ([true,false,true,true,false]++R)) =
    some (B L (ones k ++ [false,true,true,true,true,true]++R)) := by
  have h0 := turn10110 (ones k ++ false::L) R
  have h1 := sweepMany k (false::L) ([false,true,true,true,true,true]++R)
  have h := join0 h0 h1
  rw [show 11+k=k+11 by omega] at h
  simpa only [B,List.append_assoc] using h

/-- General a=1,b>=3 rule (b=3+n), arbitrary untouched tails. -/
theorem macroThree (n : Nat) (L R : List Bool) :
    run0 p (4*n+11) (B L ([true,false,true,true,true]++ones n++false::R)) =
    some (B ([false,false,true]++L) (ones n ++ [false,true,true]++R)) := by
  have h0 := turn10111 L (ones n ++ false::R)
  have h1 := macro0 0 n ([false,false,true]++L) R
  have h1' : run0 p (4*n+0+5)
      (B ([false,false,false,true]++L) (false::(ones n ++ false::R))) =
      some (B ([false,false,true]++L) (ones n ++ [false,true,true]++R)) := by
    simpa only [ones,rep,List.nil_append,Nat.add_zero] using h1
  have h := join0 h0 h1'
  rw [show 6+(4*n+0+5)=4*n+11 by omega] at h
  simpa only [List.append_assoc] using h

#print axioms seed
#print axioms macro0
#print axioms macroMany
#print axioms macroTwo
#print axioms macroThree
#print axioms turn1000
#print axioms turn1001
#print axioms terminal1010
#print axioms hole1010
end BB6.Agent32Raw421LB.Leaf4828
