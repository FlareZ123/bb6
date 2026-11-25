import SweepPumping

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw114Triple
open BB6Coverage

-- 1RB1LB_1RC0LB_0RD0RF_1LD1RE_1LA0LD_---1RA
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,3⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

abbrev tt : List Bool := [true,true]
abbrev ff : List Bool := [false,false]
abbrev ttt : List Bool := [true,true,true]
abbrev fff : List Bool := [false,false,false]
abbrev t5 : List Bool := [true,true,true,true,true]
abbrev f5 : List Bool := [false,false,false,false,false]
abbrev f9 : List Bool := [false,false,false,false,false,false,false,false,false]

def oddWord (n : Nat) (R : List Bool) : List Bool := ttt ++ rep tt (3*n) ++ R
def evenWord (n : Nat) (R : List Bool) : List Bool := ttt ++ rep tt (3*n+1) ++ true::R

/-- Runs of ones have length divisible by three. An odd run takes three
    separator zeros, an even run takes two; optional extra zeros occur in
    pairs. The final run may use implicit blank cells. -/
inductive Good : List Bool → Prop
  | nil : Good []
  | zero {R : List Bool} : Good R → Good (ff ++ R)
  | odd (n : Nat) {R : List Bool} : Good R → Good (oddWord n (fff ++ R))
  | even (n : Nat) {R : List Bool} : Good R → Good (evenWord n (ff ++ R))
  | endOdd (n : Nat) : Good (oddWord n [])
  | endEven (n : Nat) : Good (evenWord n [])

theorem goodZeros (n : Nat) {R : List Bool} (h : Good R) : Good (rep ff n ++ R) := by
  induction n with
  | zero => exact h
  | succ n ih => simpa only [rep,List.append_assoc] using Good.zero ih

theorem goodSix {R : List Bool} (h : Good R) : Good (ttt ++ ttt ++ R) := by
  cases h with
  | nil => exact Good.endEven 0
  | zero h => exact Good.even 0 h
  | odd n h =>
    simpa only [oddWord,Nat.mul_succ,rep,List.append_assoc,List.cons_append,List.nil_append] using Good.odd (n+1) h
  | even n h =>
    simpa only [evenWord,Nat.mul_succ,rep,List.append_assoc,List.cons_append,List.nil_append] using Good.even (n+1) h
  | endOdd n =>
    simpa only [oddWord,Nat.mul_succ,rep,List.append_assoc,List.cons_append,List.nil_append] using Good.endOdd (n+1)
  | endEven n =>
    simpa only [evenWord,Nat.mul_succ,rep,List.append_assoc,List.cons_append,List.nil_append] using Good.endEven (n+1)

-- A left stack consists of odd-length runs of ones after a zero. The
-- initial bottom block is 0 followed by nine ones.
def block (n : Nat) (L : List Bool) : List Bool := false :: (rep tt n ++ t5 ++ L)
inductive Stack : List Bool → Prop
  | base : Stack (block 2 [])
  | more (n : Nat) {L : List Bool} : Stack L → Stack (block n L)

def atB (L R : List Bool) : Z0 := ⟨1,L,R⟩
def baseConf (R : List Bool) : Z0 := atB [] (f9 ++ R)
def frame (L R : List Bool) : Z0 := atB ([false,true,true] ++ L) R

def Returns (z : Z0) : Prop := ∃ k R, 0 < k ∧ Good R ∧ run0 table k z = some (baseConf R)

theorem prepend {z z' : Z0} {k : Nat} (hr : run0 table k z = some z') (h : Returns z') : Returns z := by
  obtain ⟨t,R,ht,hg,h'⟩ := h
  exact ⟨k+t,R,by omega,hg,join0 hr h'⟩

theorem turn (L R : List Bool) : run0 table 11 (frame L (ff ++ R)) = some (atB L (ff ++ ttt ++ R)) := by rfl

theorem turnNil (L : List Bool) : run0 table 11 (frame L []) = some (atB L (ff ++ ttt)) := by rfl

theorem leftGadget (L R : List Bool) : run0 table 9 (atB (false::L) (ff ++ R)) = some (atB L (ttt ++ R)) := by rfl

theorem erasePair (L R : List Bool) : run0 table 2 ⟨1,[]++tt++L,[]++R⟩ = some ⟨1,[]++L,[]++ff++R⟩ := by rfl

theorem eraseFive (L R : List Bool) : run0 table 5 (atB (t5 ++ L) R) = some (atB L (f5 ++ R)) := by rfl

theorem leftMove (n : Nat) (L U : List Bool) :
    run0 table (14+2*n) (atB (block n L) (ff ++ U)) = some (atB L (f5 ++ rep ff n ++ ttt ++ U)) := by
  have h1 := leftGadget (rep tt n ++ t5 ++ L) U
  have h2 := sweepL table 1 [] [] tt ff 2 erasePair n (t5 ++ L) (ttt ++ U)
  have h2' : run0 table (2*n) (atB (rep tt n ++ t5 ++ L) (ttt ++ U)) = some (atB (t5 ++ L) (rep ff n ++ ttt ++ U)) := by
    simpa only [atB,List.nil_append,List.append_assoc] using h2
  have h3 := eraseFive L (rep ff n ++ ttt ++ U)
  have H := join0 (join0 h1 h2') h3
  rw [show 9+2*n+5=14+2*n by omega] at H
  simpa only [block,List.append_assoc] using H

theorem leftReturn (L : List Bool) (h : Stack L) (U : List Bool) (hu : Good (ttt ++ U)) : Returns (atB L (ff ++ U)) := by
  induction h generalizing U with
  | base => exact ⟨18,ttt ++ U,by omega,hu,leftMove 2 [] U⟩
  | more n h ih =>
    have hg : Good (ttt ++ (fff ++ rep ff n ++ ttt ++ U)) := by
      have H := Good.odd 0 (goodZeros n hu)
      simpa only [oddWord,Nat.mul_zero,rep,List.nil_append,List.append_assoc] using H
    exact prepend (leftMove n _ U) (ih (fff ++ rep ff n ++ ttt ++ U) hg)

-- The right scan begins with a three-one prefix and then consumes pairs of
-- ones in state D. The two exits consume parity-matched separators.
theorem rightStart (L R : List Bool) : run0 table 7 (frame L (ttt ++ R)) = some ⟨3,[true,false,true,true,true,true]++L,R⟩ := by rfl

theorem rightPair (L R : List Bool) :
    run0 table 12 ⟨3,[true,false,true,true,true,true]++L,[]++tt++R⟩ = some ⟨3,[true,false,true,true,true,true]++tt++L,[]++R⟩ := by rfl

theorem exitOdd (L R : List Bool) : run0 table 7 ⟨3,[true,false,true,true,true,true]++L,fff++R⟩ = some (frame (false::(t5++L)) R) := by rfl

theorem exitEven (L R : List Bool) : run0 table 9 ⟨3,[true,false,true,true,true,true]++L,true::(ff++R)⟩ = some (frame (false::(t5++L)) R) := by rfl

theorem exitOddNil (L : List Bool) : run0 table 7 ⟨3,[true,false,true,true,true,true]++L,[]⟩ = some (frame (false::(t5++L)) []) := by rfl

theorem exitEvenNil (L : List Bool) : run0 table 9 ⟨3,[true,false,true,true,true,true]++L,[true]⟩ = some (frame (false::(t5++L)) []) := by rfl

theorem commuteFive (n : Nat) : t5 ++ rep tt n = rep tt n ++ t5 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change tt ++ (t5 ++ rep tt n) = tt ++ (rep tt n ++ t5)
    rw [ih]

theorem rightScan (n : Nat) (L R : List Bool) :
    run0 table (7+12*n) (frame L (ttt ++ rep tt n ++ R)) =
      some ⟨3,[true,false,true,true,true,true]++rep tt n++L,R⟩ := by
  have h1 := rightStart L (rep tt n ++ R)
  have h2 := sweepR table 3 [true,false,true,true,true,true] [] tt tt 12 rightPair n L R
  simpa only [List.nil_append,List.append_assoc] using join0 h1 (by simpa only [List.nil_append,List.append_assoc] using h2)

theorem oddMove (n : Nat) (L R : List Bool) :
    run0 table (7+12*(3*n)+7) (frame L (oddWord n (fff ++ R))) = some (frame (block (3*n) L) R) := by
  have h1 := rightScan (3*n) L (fff++R)
  have h2 := exitOdd (rep tt (3*n) ++ L) R
  have H := join0 h1 (by simpa only [List.append_assoc] using h2)
  simpa only [oddWord,block,List.append_assoc,← List.append_assoc t5 (rep tt (3*n)) L,commuteFive] using H

theorem evenMove (n : Nat) (L R : List Bool) :
    run0 table (7+12*(3*n+1)+9) (frame L (evenWord n (ff ++ R))) = some (frame (block (3*n+1) L) R) := by
  have h1 := rightScan (3*n+1) L (true::(ff++R))
  have h2 := exitEven (rep tt (3*n+1) ++ L) R
  have H := join0 h1 (by simpa only [List.append_assoc] using h2)
  simpa only [evenWord,block,List.append_assoc,← List.append_assoc t5 (rep tt (3*n+1)) L,commuteFive] using H

theorem oddEndMove (n : Nat) (L : List Bool) :
    run0 table (7+12*(3*n)+7) (frame L (oddWord n [])) = some (frame (block (3*n) L) []) := by
  have h1 := rightScan (3*n) L []
  have h2 := exitOddNil (rep tt (3*n) ++ L)
  have H := join0 h1 (by simpa only [List.append_assoc] using h2)
  simpa only [oddWord,block,List.append_assoc,← List.append_assoc t5 (rep tt (3*n)) L,commuteFive] using H

theorem evenEndMove (n : Nat) (L : List Bool) :
    run0 table (7+12*(3*n+1)+9) (frame L (evenWord n [])) = some (frame (block (3*n+1) L) []) := by
  have h1 := rightScan (3*n+1) L [true]
  have h2 := exitEvenNil (rep tt (3*n+1) ++ L)
  have H := join0 h1 (by simpa only [List.append_assoc] using h2)
  simpa only [evenWord,block,List.append_assoc,← List.append_assoc t5 (rep tt (3*n+1)) L,commuteFive] using H

theorem turnReturn (L : List Bool) (h : Stack L) : Returns (frame L []) :=
  prepend (turnNil L) (leftReturn L h ttt (goodSix Good.nil))

theorem scan (R : List Bool) (h : Good R) (L : List Bool) (hl : Stack L) : Returns (frame L R) := by
  induction h generalizing L with
  | nil => exact turnReturn L hl
  | zero h ih => exact prepend (turn L _) (leftReturn L hl (ttt ++ _) (goodSix h))
  | odd n h ih => exact prepend (oddMove n L _) (ih (block (3*n) L) (Stack.more _ hl))
  | even n h ih => exact prepend (evenMove n L _) (ih (block (3*n+1) L) (Stack.more _ hl))
  | endOdd n => exact prepend (oddEndMove n L) (turnReturn _ (Stack.more _ hl))
  | endEven n => exact prepend (evenEndMove n L) (turnReturn _ (Stack.more _ hl))

theorem enterFrame (R : List Bool) : run0 table 105 (baseConf R) = some (frame (block 2 []) R) := by rfl

theorem returnBase (R : List Bool) (h : Good R) : Returns (baseConf R) := prepend (enterFrame R) (scan R h _ Stack.base)

-- Dependent state type keeps the right-language witness through iteration.
noncomputable def next (s : {R : List Bool // Good R}) : {R : List Bool // Good R} :=
  ⟨Classical.choose (Classical.choose_spec (returnBase s.val s.property)), (Classical.choose_spec (Classical.choose_spec (returnBase s.val s.property))).2.1⟩
noncomputable def cost (s : {R : List Bool // Good R}) : Nat := Classical.choose (returnBase s.val s.property)
theorem cost_pos (s : {R : List Bool // Good R}) : 0 < cost s := (Classical.choose_spec (Classical.choose_spec (returnBase s.val s.property))).1
theorem ret (s : {R : List Bool // Good R}) : run0 table (cost s) (baseConf s.val) = some (baseConf (next s).val) := (Classical.choose_spec (Classical.choose_spec (returnBase s.val s.property))).2.2

noncomputable def words : Nat → {R : List Bool // Good R}
  | 0 => ⟨ff ++ ff ++ evenWord 0 [],Good.zero (Good.zero (Good.endEven 0))⟩
  | n+1 => next (words n)

theorem entry : run0 table 206 ⟨0,[],[]⟩ = some (baseConf (words 0).val) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table (fun n => baseConf (words n).val) 206 (fun n => cost (words n)) entry
    (fun n => cost_pos (words n)) (fun n => ret (words n)) m hm
#print axioms never
end BB6Coverage.Agent31Pump.Raw114Triple
