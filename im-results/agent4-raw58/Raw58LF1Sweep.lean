import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4LF1Sweep
open BB6Coverage Agent31Pump

inductive V where | v86 | v109 | v122 deriving DecidableEq, Repr

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some (if v = .v109 then ⟨false,false,3⟩ else ⟨true,true,2⟩))
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,decide (v ≠ .v86),2⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def cost1 (v : V) : Nat := if v = .v109 then 3 else 1
def cost010 (v : V) : Nat := if v = .v86 then 5 else 3

def cursor (q : Fin 6) (L R : List Bool) : Z0 := ⟨q,R.headD false::L,R.tail⟩

theorem beginScan (v : V) (R : List Bool) :
    run0 (table v) 2 ⟨0,[],false::R⟩ = some (cursor 2 [true,true] R) := by cases v <;> rfl

theorem c1 (v : V) (L R : List Bool) :
    run0 (table v) (cost1 v) (cursor 2 (true::L) (true::R)) =
      some (cursor 2 (true::true::L) R) := by cases v <;> rfl

theorem c010 (v : V) (L R : List Bool) :
    run0 (table v) (cost010 v) (cursor 2 (true::L) (false::true::false::R)) =
      some (cursor 2 (true::true::false::true::L) R) := by cases v <;> rfl

theorem c010end (v : V) (L : List Bool) :
    run0 (table v) (cost010 v) (cursor 2 (true::L) [false,true]) =
      some (cursor 2 (true::true::false::true::L) []) := by cases v <;> rfl

theorem c01100 (v : V) (L R : List Bool) :
    run0 (table v) 5 (cursor 2 (true::L) (false::true::true::false::false::R)) =
      some (cursor 2 (true::true::false::true::false::true::L) R) := by cases v <;> rfl

theorem c01100end (v : V) (L : List Bool) :
    run0 (table v) 5 (cursor 2 (true::L) [false,true,true]) =
      some (cursor 2 (true::true::false::true::false::true::L) []) := by cases v <;> rfl

theorem c01101 (v : V) (L R : List Bool) :
    run0 (table v) 4 (cursor 2 (true::L) (false::true::true::false::true::R)) =
      some ⟨1,true::true::false::true::false::true::L,R⟩ := by cases v <;> rfl

theorem c0111 (v : V) (L R : List Bool) :
    run0 (table v) 3 (cursor 2 (true::L) (false::true::true::true::R)) =
      some ⟨0,true::false::true::false::true::L,R⟩ := by cases v <;> rfl

theorem c00 (v : V) (L R : List Bool) :
    run0 (table v) 5 (cursor 2 (true::L) (false::false::R)) =
      some ⟨0,true::false::true::L,R⟩ := by cases v <;> rfl

theorem c00end (v : V) (L : List Bool) :
    run0 (table v) 5 (cursor 2 (true::L) []) =
      some ⟨0,true::false::true::L,[]⟩ := by cases v <;> rfl

abbrev ones (n : Nat) := rep [true] n
abbrev zeros (n : Nat) := rep [false] n

def word : List Nat → List Bool
  | [] => []
  | a::w => zeros a ++ true::word w

def leftTail : List Nat → List Bool
  | [] => []
  | k::ks => false::(ones (k+1) ++ leftTail ks)

def left (k : Nat) (ks : List Nat) : List Bool := ones (k+1) ++ leftTail ks

def finishRuns (k : Nat) (ks w : List Nat) : List Nat :=
  match ks with
  | [] => (k+1)::w
  | a::as => finishRuns a as ((k+1)::w)

def finishCost (k : Nat) (ks : List Nat) : Nat :=
  match ks with
  | [] => k+2
  | a::as => k+2+finishCost a as

theorem fSweep (v : V) (k : Nat) (L R : List Bool) :
    run0 (table v) k ⟨5,ones k ++ L,R⟩ = some ⟨5,L,zeros k ++ R⟩ := by
  simpa only [Nat.one_mul,List.nil_append] using
    sweepL (table v) 5 [] [] [true] [false] 1 (by intro L R; cases v <;> rfl) k L R

theorem aBlock (v : V) (k : Nat) (L R : List Bool) :
    run0 (table v) (k+2) ⟨0,ones (k+1) ++ false::L,R⟩ =
      some ⟨0,L,zeros (k+1) ++ true::R⟩ := by
  have h1 : run0 (table v) 1 ⟨0,ones (k+1) ++ false::L,R⟩ = some ⟨5,ones k ++ false::L,true::R⟩ := by cases v <;> rfl
  have h2 := fSweep v k (false::L) (true::R)
  have h3 : run0 (table v) 1 ⟨5,false::L,zeros k ++ true::R⟩ = some ⟨0,L,zeros (k+1) ++ true::R⟩ := by cases v <;> rfl
  have h := join0 (join0 h1 h2) h3
  rw [show 1+k+1 = k+2 by omega] at h
  exact h

theorem aBlockEnd (v : V) (k : Nat) (R : List Bool) :
    run0 (table v) (k+2) ⟨0,ones (k+1),R⟩ =
      some ⟨0,[],zeros (k+1) ++ true::R⟩ := by
  have h1 : run0 (table v) 1 ⟨0,ones (k+1),R⟩ = some ⟨5,ones k,true::R⟩ := by cases v <;> rfl
  have h2 := fSweep v k [] (true::R)
  have h3 : run0 (table v) 1 ⟨5,[],zeros k ++ true::R⟩ = some ⟨0,[],zeros (k+1) ++ true::R⟩ := by cases v <;> rfl
  rw [List.append_nil] at h2
  have h := join0 (join0 h1 h2) h3
  rw [show 1+k+1 = k+2 by omega] at h
  exact h

theorem aReturn (v : V) (k : Nat) (ks w : List Nat) :
    run0 (table v) (finishCost k ks) ⟨0,left k ks,word w⟩ =
      some ⟨0,[],word (finishRuns k ks w)⟩ := by
  induction ks generalizing k w with
  | nil => simpa only [left,leftTail,List.append_nil,finishCost,finishRuns,word] using aBlockEnd v k (word w)
  | cons a as ih =>
    have h1 := aBlock v k (left a as) (word w)
    have h2 := ih a ((k+1)::w)
    exact join0 h1 h2

inductive Result where
  | back (cost : Nat) (w : List Nat)
  | hole (cost : Nat)
  deriving DecidableEq, Repr

def Result.add (n : Nat) : Result → Result
  | .back c w => .back (n+c) w
  | .hole c => .hole (n+c)

def read0 (z : Z0) : Fin 6 × Bool := (z.q,z.l.headD false)

def Valid (v : V) (z : Z0) : Result → Prop
  | .back c w => run0 (table v) c z = some ⟨0,[],word w⟩
  | .hole c => (run0 (table v) c z).map read0 = some (1,true)

theorem validAdd (v : V) (n : Nat) (a b : Z0) (o : Result)
    (h : run0 (table v) n a = some b) (hv : Valid v b o) : Valid v a (o.add n) := by
  cases o with
  | back c w => exact join0 h hv
  | hole c =>
    change (run0 (table v) (n+c) a).map read0 = _
    rw [run0_add,h]
    exact hv

def cState (k : Nat) (ks : List Nat) (w : List Nat) : Z0 := cursor 2 (left (k+1) ks) (word w)

def finish00 (k : Nat) (ks w : List Nat) : Result :=
  .back (5+finishCost 0 ((k+1)::ks)) (finishRuns 0 ((k+1)::ks) w)

def finish0111 (k : Nat) (ks w : List Nat) : Result :=
  .back (3+finishCost 0 (0::(k+1)::ks)) (finishRuns 0 (0::(k+1)::ks) w)

theorem finish00_sound (v : V) (k : Nat) (ks w : List Nat) (a : Nat) :
    Valid v (cState k ks ((a+2)::w)) (finish00 k ks (a::w)) := by
  have h1 := c00 v (ones (k+1) ++ leftTail ks) (word (a::w))
  have h2 := aReturn v 0 ((k+1)::ks) (a::w)
  exact join0 h1 h2

theorem finish00end_sound (v : V) (k : Nat) (ks : List Nat) :
    Valid v (cState k ks []) (finish00 k ks []) := by
  have h1 := c00end v (ones (k+1) ++ leftTail ks)
  have h2 := aReturn v 0 ((k+1)::ks) []
  exact join0 h1 h2

theorem finish0111_sound (v : V) (k : Nat) (ks w : List Nat) :
    Valid v (cState k ks (1::0::0::w)) (finish0111 k ks w) := by
  have h1 := c0111 v (ones (k+1) ++ leftTail ks) (word w)
  have h2 := aReturn v 0 (0::(k+1)::ks) w
  exact join0 h1 h2

theorem hole_sound (v : V) (k : Nat) (ks w : List Nat) :
    Valid v (cState k ks (1::0::1::w)) (.hole 4) := by
  have h := c01101 v (ones (k+1) ++ leftTail ks) (word w)
  change (run0 (table v) 4 (cState k ks (1::0::1::w))).map read0 = _
  rw [show run0 (table v) 4 (cState k ks (1::0::1::w)) = _ from h]
  rfl

theorem c1_sound (v : V) (k : Nat) (ks w : List Nat) :
    run0 (table v) (cost1 v) (cState k ks (0::w)) = some (cState (k+1) ks w) := by
  exact c1 v (ones (k+1) ++ leftTail ks) (word w)

theorem c010_sound (v : V) (k : Nat) (ks w : List Nat) (a : Nat) :
    run0 (table v) (cost010 v) (cState k ks (1::(a+1)::w)) =
      some (cState 0 ((k+1)::ks) (a::w)) := by
  exact c010 v (ones (k+1) ++ leftTail ks) (word (a::w))

theorem c010end_sound (v : V) (k : Nat) (ks : List Nat) :
    run0 (table v) (cost010 v) (cState k ks [1]) = some (cState 0 ((k+1)::ks) []) := by
  exact c010end v (ones (k+1) ++ leftTail ks)

theorem c01100_sound (v : V) (k : Nat) (ks w : List Nat) (a : Nat) :
    run0 (table v) 5 (cState k ks (1::0::(a+2)::w)) =
      some (cState 0 (0::(k+1)::ks) (a::w)) := by
  exact c01100 v (ones (k+1) ++ leftTail ks) (word (a::w))

theorem c01100end_sound (v : V) (k : Nat) (ks : List Nat) :
    run0 (table v) 5 (cState k ks [1,0]) = some (cState 0 (0::(k+1)::ks) []) := by
  exact c01100end v (ones (k+1) ++ leftTail ks)

-- The cursor is given the remaining number of zeros before the next 1,
-- and the later zero-run counts. Every recursion removes at least one 1.
def evalC (v : V) (k : Nat) (ks : List Nat) (a : Nat) (w : List Nat) : Result :=
  match a,w with
  | 0,[] => (finish00 (k+1) ks []).add (cost1 v)
  | 0,b::bs => (evalC v (k+1) ks b bs).add (cost1 v)
  | 1,[] => (finish00 0 ((k+1)::ks) []).add (cost010 v)
  | 1,0::[] => (finish00 0 (0::(k+1)::ks) []).add 5
  | 1,0::0::bs => finish0111 k ks bs
  | 1,0::1::_bs => .hole 4
  | 1,0::(b+2)::bs => (evalC v 0 (0::(k+1)::ks) b bs).add 5
  | 1,(b+1)::bs => (evalC v 0 ((k+1)::ks) b bs).add (cost010 v)
  | a+2,bs => finish00 k ks (a::bs)
termination_by structural w

theorem evalC_sound (v : V) (k : Nat) (ks : List Nat) (a : Nat) (w : List Nat) :
    Valid v (cState k ks (a::w)) (evalC v k ks a w) := by
  match a,w with
  | 0,[] => exact validAdd v _ _ _ _ (c1_sound v k ks []) (finish00end_sound v (k+1) ks)
  | 0,b::bs => exact validAdd v _ _ _ _ (c1_sound v k ks (b::bs)) (evalC_sound v (k+1) ks b bs)
  | 1,[] => exact validAdd v _ _ _ _ (c010end_sound v k ks) (finish00end_sound v 0 ((k+1)::ks))
  | 1,0::[] => exact validAdd v _ _ _ _ (c01100end_sound v k ks) (finish00end_sound v 0 (0::(k+1)::ks))
  | 1,0::0::bs => exact finish0111_sound v k ks bs
  | 1,0::1::bs => exact hole_sound v k ks bs
  | 1,0::(b+2)::bs => exact validAdd v _ _ _ _ (c01100_sound v k ks bs b) (evalC_sound v 0 (0::(k+1)::ks) b bs)
  | 1,(b+1)::bs => exact validAdd v _ _ _ _ (c010_sound v k ks bs b) (evalC_sound v 0 ((k+1)::ks) b bs)
  | a+2,bs => cases bs <;> exact finish00_sound v k ks _ a
termination_by structural w


-- One sweep section starting at the left edge in state A.
def evalSection (v : V) (w : List Nat) : Result :=
  match w with
  | [] => (finish00 0 [] []).add 2
  | 0::_ws => .hole 1
  | (a+1)::ws => (evalC v 0 [] a ws).add 2

theorem evalSection_sound (v : V) (w : List Nat) :
    Valid v ⟨0,[],word w⟩ (evalSection v w) := by
  match w with
  | [] => exact validAdd v _ _ _ _ (show run0 (table v) 2 ⟨0,[],[]⟩ = some (cState 0 [] []) from by cases v <;> rfl) (finish00end_sound v 0 [])
  | 0::ws => cases v <;> rfl
  | (a+1)::ws => exact validAdd v _ _ _ _ (beginScan v (word (a::ws))) (evalC_sound v 0 [] a ws)

def evalSections (v : V) : Nat → List Nat → Result
  | 0,w => .back 0 w
  | n+1,w => match evalSection v w with
    | .hole c => .hole c
    | .back c w' => (evalSections v n w').add c

theorem evalSections_sound (v : V) (n : Nat) (w : List Nat) :
    Valid v ⟨0,[],word w⟩ (evalSections v n w) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    have h := evalSection_sound v w
    cases he : evalSection v w with
    | hole c => simpa only [evalSections,he] using he ▸ h
    | back c w' =>
      rw [he] at h
      simpa only [evalSections,he] using validAdd v c _ _ _ h (ih w')

theorem entry (v : V) : run0 (table v) 12 ⟨0,[],[]⟩ = some ⟨0,[],word [2,1]⟩ := by cases v <;> rfl

def blankEval (v : V) (n : Nat) : Result := (evalSections v n [2,1]).add 12

theorem blankEval_sound (v : V) (n : Nat) : Valid v ⟨0,[],[]⟩ (blankEval v n) :=
  validAdd v 12 _ _ _ (entry v) (evalSections_sound v n [2,1])

#print axioms blankEval_sound
end BB6Coverage.Agent4LF1Sweep
