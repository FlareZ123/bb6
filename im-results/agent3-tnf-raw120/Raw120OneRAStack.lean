import SweepPumping
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace BB6.Agent3Raw120OneRAStack
open BB6Coverage BB6Coverage.Agent31Pump

/-- Leaves 1602 and 1606 differ only at B1. Their unary-run recursion
    is identical; the B1-dependent split costs 9 or 11 steps. -/
def table (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,if v then 2 else 1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

abbrev O (n : Nat) := List.replicate n true

def splitCost (v : Bool) : Nat := if v then 11 else 9

theorem splitRaw (v : Bool) (L R : List Bool) :
    run0 (table v) (splitCost v) ⟨4,false::L,true::true::true::R⟩ =
      some ⟨4,L,true::true::false::true::R⟩ := by cases v <;> rfl

theorem splitRoot (v : Bool) (R : List Bool) :
    run0 (table v) (splitCost v) ⟨4,[],true::true::true::R⟩ =
      some ⟨4,[],true::true::false::true::R⟩ := by cases v <;> rfl

theorem sweep (v : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v) n ⟨4,O n++L,R⟩ = some ⟨4,L,O n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 (table v) 1 ⟨4,true::(O n++L),R⟩ = some ⟨4,O n++L,true::R⟩ := by rfl
    have H := join0 h (ih (true::R))
    rw [show 1+n=n+1 by omega] at H
    have he : O n ++ true::R = true::(O n++R) := by
      change O n ++ ([true]++R) = ([true]++O n)++R
      rw [← List.append_assoc,show [true]=O 1 by rfl,
        List.replicate_append_replicate,List.replicate_append_replicate,Nat.add_comm n 1]
    rw [he] at H
    exact H

theorem pop (v : Bool) (k n : Nat) (L R : List Bool) :
    run0 (table v) (splitCost v+k) ⟨4,false::(O k++L),O (n+3)++R⟩ =
      some ⟨4,L,O (k+2)++false::(O (n+1)++R)⟩ := by
  have h := join0 (splitRaw v (O k++L) (O n++R))
    (sweep v k L (true::true::false::true::(O n++R)))
  have he : O k++true::true::false::true::(O n++R) =
      O (k+2)++false::(O (n+1)++R) := by
    change O k++(O 2++false::(O (n+1)++R)) = _
    rw [← List.append_assoc,List.replicate_append_replicate]
  rw [he] at h
  exact h

theorem moveOne (v : Bool) (L R : List Bool) :
    run0 (table v) 7 ⟨4,false::L,true::true::false::true::R⟩ =
      some ⟨4,false::true::L,true::true::false::R⟩ := by rfl

theorem moveRoot (v : Bool) (R : List Bool) :
    run0 (table v) 7 ⟨4,[],true::true::false::true::R⟩ =
      some ⟨4,[false,true],true::true::false::R⟩ := by rfl

theorem scan (v : Bool) (m : Nat) (L R : List Bool) :
    run0 (table v) (7*m) ⟨4,false::L,true::true::false::(O m++R)⟩ =
      some ⟨4,false::(O m++L),true::true::false::R⟩ := by
  induction m generalizing L with
  | zero => rfl
  | succ m ih =>
    have H := join0 (moveOne v L (O m++R)) (ih (true::L))
    rw [show 7*(m+1)=7+7*m by omega]
    have he : O m ++ true::L = true::(O m++L) := by
      change O m ++ ([true]++L) = ([true]++O m)++L
      rw [← List.append_assoc,show [true]=O 1 by rfl,
        List.replicate_append_replicate,List.replicate_append_replicate,Nat.add_comm m 1]
    rw [he] at H
    exact H

theorem scanAdd (v : Bool) (k m : Nat) (L R : List Bool) :
    run0 (table v) (7*m) ⟨4,false::(O k++L),true::true::false::(O m++R)⟩ =
      some ⟨4,false::(O (k+m)++L),true::true::false::R⟩ := by
  have H := scan v m (O k++L) R
  rw [← List.append_assoc,List.replicate_append_replicate,Nat.add_comm m k] at H
  exact H

theorem endThree (v : Bool) (L : List Bool) :
    run0 (table v) 11 ⟨4,false::L,[true,true,false]⟩ =
      some ⟨4,false::true::L,O 4⟩ := by rfl

theorem endTwo (v : Bool) (L : List Bool) :
    run0 (table v) 11 ⟨4,false::L,[true,true]⟩ =
      some ⟨4,false::true::L,O 4⟩ := by rfl

theorem push (v : Bool) (L R : List Bool) :
    run0 (table v) 8 ⟨4,false::L,true::true::false::false::true::true::R⟩ =
      some ⟨4,false::true::true::false::true::L,true::true::R⟩ := by rfl

/-- The grammar admits a singleton run only as the second member of a pair
    whose first run has length two. It is closed under the full macro. -/
inductive Tail where
  | nil
  | singleTwo
  | pair (m : Nat) (tail : Tail) -- lengths 2, m+1
  | big (r : Nat) (tail : Tail) -- length r+3
  deriving Repr

def word : Tail → List Bool
  | .nil => []
  | .singleTwo => [false,true,true]
  | .pair m t => false::true::true::false::(O (m+1)++word t)
  | .big r t => false::(O (r+3)++word t)

def next : Tail → Tail
  | .nil => .singleTwo
  | .singleTwo => .big 0 .singleTwo
  | .pair m t => .big (m+1) (next t)
  | .big r t => .pair r t

/-- A rightward scan of the current unary run followed by the complete
    recursive processing of its tail and leftward unwind. L is arbitrary. -/
theorem process (v : Bool) (t : Tail) (k m : Nat) (L : List Bool) :
    ∃ time, 0 < time ∧
      run0 (table v) time ⟨4,false::(O k++L),true::true::false::(O m++word t)⟩ =
        some ⟨4,L,O (k+m+3)++word (next t)⟩ := by
  induction t generalizing k m L with
  | nil =>
    have h1 := scanAdd v k m L []
    have h2 := endThree v (O (k+m)++L)
    have h3 := pop v (k+m+1) 1 L []
    have H := join0 (join0 h1 h2) h3
    refine ⟨7*m+11+(splitCost v+(k+m+1)),by omega,?_⟩
    simpa only [word,next,List.append_nil,show k+m+1+2=k+m+3 by omega,show O (1+1)=[true,true] by rfl] using H
  | singleTwo =>
    have h1 := scanAdd v k m L [false,true,true]
    have h2 := push v (O (k+m)++L) []
    have h3 := endTwo v (O 2++false::(O (k+m+1)++L))
    have h4 := pop v 3 1 (false::(O (k+m+1)++L)) []
    have h5 := pop v (k+m+1) 2 L [false,true,true]
    have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
    refine ⟨7*m+8+11+(splitCost v+3)+(splitCost v+(k+m+1)),by omega,?_⟩
    simpa only [word,next,List.append_nil,show k+m+1+2=k+m+3 by omega,show O (1+1)=[true,true] by rfl] using H
  | pair a t ih =>
    have h1 := scanAdd v k m L (word (.pair a t))
    have h2 := push v (O (k+m)++L) (false::(O (a+1)++word t))
    obtain ⟨time,ht,h3⟩ := ih 2 (a+1) (false::(O (k+m+1)++L))
    have h4 := pop v (k+m+1) (a+3) L (word (next t))
    rw [show a+3+3=2+(a+1)+3 by omega] at h4
    have H := join0 (join0 (join0 h1 h2) h3) h4
    refine ⟨7*m+8+time+(splitCost v+(k+m+1)),by omega,?_⟩
    simpa only [word,next,show k+m+1+2=k+m+3 by omega,
      show a+3+1=a+1+3 by omega] using H
  | big a t =>
    have h1 := scanAdd v k m L (word (.big a t))
    have h2 := push v (O (k+m)++L) (O (a+1)++word t)
    have h3 := pop v 2 a (false::(O (k+m+1)++L)) (word t)
    have h4 := pop v (k+m+1) 1 L (false::(O (a+1)++word t))
    have H := join0 (join0 (join0 h1 h2) h3) h4
    refine ⟨7*m+8+(splitCost v+2)+(splitCost v+(k+m+1)),by omega,?_⟩
    simpa only [word,next,List.cons_append,List.nil_append,show k+m+1+2=k+m+3 by omega,show O (1+1)=[true,true] by rfl] using H

/-- At the left blank boundary the first unary run increases by one, and
    the remaining run grammar evolves by next, with positive primitive cost. -/
def cfg (n : Nat) (t : Tail) : Z0 := ⟨4,[],O (n+4)++word t⟩

theorem advance (v : Bool) (n : Nat) (t : Tail) :
    ∃ time, 0 < time ∧ run0 (table v) time (cfg n t) = some (cfg (n+1) (next t)) := by
  have h1 := splitRoot v (O (n+1)++word t)
  have h2 := moveRoot v (O (n+1)++word t)
  obtain ⟨time,ht,h3⟩ := process v t 1 (n+1) []
  have H := join0 (join0 h1 h2) h3
  refine ⟨splitCost v+7+time,by omega,?_⟩
  simp only [cfg]
  rw [show n+4=(n+1)+3 by omega]
  simpa only [List.append_nil,List.replicate_succ,List.cons_append,show 1+(n+1)+3=n+1+4 by omega] using H

theorem entry (v : Bool) : run0 (table v) 9 ⟨0,[],[]⟩ = some (cfg 0 .nil) := by rfl

def iter : Nat → Tail
  | 0 => .nil
  | n+1 => next (iter n)

def family (n : Nat) : Z0 := cfg n (iter n)

noncomputable def cost (v : Bool) (n : Nat) : Nat :=
  Classical.choose (advance v n (iter n))

theorem positive (v : Bool) (n : Nat) : 0 < cost v n :=
  (Classical.choose_spec (advance v n (iter n))).1

theorem growth (v : Bool) (n : Nat) :
    run0 (table v) (cost v n) (family n) = some (family (n+1)) :=
  (Classical.choose_spec (advance v n (iter n))).2

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family 9 (cost v) (entry v) (positive v) (growth v) m hm

#print axioms advance
#print axioms growth
#print axioms never
end BB6.Agent3Raw120OneRAStack
