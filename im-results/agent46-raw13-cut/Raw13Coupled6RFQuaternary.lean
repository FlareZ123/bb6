import SweepPumping
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled6RFQuaternary
open BB6Coverage BB6Coverage.Agent31Pump

def p : PartialMachine := FAR.fromCodes [7,14,11,12,2,19,12,0,5,21,6,24]
abbrev A (l r : List Bool) : Z0 := ⟨0,l,r⟩
abbrev E (l r : List Bool) : Z0 := ⟨4,l,r⟩
abbrev P : List Bool := [false,true,false]
abbrev X : List Bool := [true,true,false]
abbrev Y : List Bool := [false,false,true]
abbrev Z : List Bool := [true,true,true]
abbrev H : List Bool := [true,false]
abbrev J : List Bool := [false,true]
abbrev M : List Bool := [true,true,true,true,false]

inductive Digit | d0 | d1 | d2 | d3
  deriving DecidableEq

def pair : Digit → List Bool
  | .d0 => [true,false]
  | .d1 => [false,false]
  | .d2 => [true,true]
  | .d3 => [false,true]
def digit (d : Digit) : List Bool := false :: pair d

def enc : List Digit → List Bool
  | [] => []
  | d::ds => digit d ++ enc ds

def suffix : List Digit → List Bool
  | [] => []
  | d::ds => pair d ++ enc ds

def inc : List Digit → List Digit
  | [] => [.d2]
  | .d0::ds => .d1::ds
  | .d1::ds => .d2::ds
  | .d2::ds => .d3::ds
  | .d3::ds => .d0::inc ds

def root (n : Nat) (phase : List Bool) (ds : List Digit) : Z0 :=
  A [] (rep P (n+1) ++ phase ++ enc ds)

-- The right sweep reads one three-bit block at a time, preserving all tails.
theorem first (R : List Bool) : run0 p 3 (A [] (P++R)) = some (E (false::Z) R) := rfl
theorem forward (L R : List Bool) : run0 p 3 (E (false::L) (P++R)) = some (E (false::(X++L)) R) := rfl

theorem enter (n : Nat) (R : List Bool) :
    run0 p (3+3*n) (A [] (rep P (n+1)++R)) = some (E (false::(rep X n++Z)) R) := by
  have h := first (rep P n++R)
  have h' := sweepR p 4 [false] [] P X 3 (by intro L R; exact forward L R) n Z R
  have j := join0 h h'
  simpa only [E,rep,List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using j

theorem backBlock (L R : List Bool) : run0 p 3 (A (H++X++L) R) = some (A (H++L) (Y++R)) := rfl

theorem backSweep (n : Nat) (L R : List Bool) :
    run0 p (3*n) (A (H++rep X n++L) R) = some (A (H++L) (rep Y n++R)) := by
  simpa only [List.nil_append] using sweepL p 0 H [] X Y 3 (by intro L R; exact backBlock L R) n L R

theorem finish (R : List Bool) : run0 p 5 (A (H++Z) R) = some (A [] (P++J++R)) := rfl

theorem rot (n : Nat) : J ++ rep Y n = rep P n ++ J := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,←List.append_assoc,show J++Y=P++J by rfl,List.append_assoc,ih,←List.append_assoc,←rep]

theorem back (n : Nat) (R : List Bool) :
    run0 p (3*n+5) (A (H++rep X n++Z) R) = some (A [] (rep P (n+1)++J++R)) := by
  have h := backSweep n Z R
  have j := join0 h (finish (rep Y n++R))
  rw [show P++J++(rep Y n++R) = rep P (n+1)++J++R by
    simp only [List.append_assoc,rep]
    rw [←List.append_assoc J,rot,List.append_assoc]] at j
  exact j

-- The first two passes change the small phase marker and leave the digit word unchanged.
theorem phase1zero (R : List Bool) :
    run0 p 6 (E (false::Z) (H++R)) = some (A [] (P++[false,false,false]++R)) := rfl

theorem phase1step (L R : List Bool) :
    run0 p 4 (E (false::(X++L)) (H++R)) = some (A (H++L) ([false,false,false,false]++R)) := rfl

theorem phase1 (n : Nat) (ds : List Digit) : ∃ t, 0<t ∧
    run0 p t (root n H ds) = some (root n [false,false,false] ds) := by
  have h := enter n (H++enc ds)
  cases n with
  | zero => exact ⟨9,by decide,join0 h (phase1zero (enc ds))⟩
  | succ n =>
    have h' := phase1step (rep X n++Z) (enc ds)
    have j := join0 h h'
    have z := join0 j (back n ([false,false,false,false]++enc ds))
    refine ⟨3+3*(n+1)+4+(3*n+5),by omega,?_⟩
    have eq : rep P (n+1)++J++([false,false,false,false]++enc ds) = rep P (n+1+1)++[false,false,false]++enc ds := by
      have hh : rep P (n+1)++P = rep P (n+1+1) := rep_snoc P (n+1)
      rw [List.append_assoc,show J++([false,false,false,false]++enc ds)=P++([false,false,false]++enc ds) by rfl,←List.append_assoc,hh,List.append_assoc]
    rw [eq] at z
    simpa only [root,List.append_assoc] using z

theorem phase2step (L R : List Bool) :
    run0 p 3 (E (false::L) ([false,false,false]++R)) = some (A (H++L) (H++R)) := rfl

theorem phase2 (n : Nat) (ds : List Digit) : ∃ t, 0<t ∧
    run0 p t (root n [false,false,false] ds) = some (root n [false,true,true,false] ds) := by
  have h := enter n ([false,false,false]++enc ds)
  have h' := phase2step (rep X n++Z) (enc ds)
  have j := join0 (join0 h h') (back n (H++enc ds))
  refine ⟨3+3*n+3+(3*n+5),by omega,?_⟩
  rw [List.append_assoc (rep P (n+1)) J,show J++(H++enc ds) = [false,true,true,false]++enc ds by rfl] at j
  simpa only [root,List.append_assoc] using j

-- In the third pass, leading digit3 blocks are transferred to the left.
theorem prepare (L : List Bool) (ds : List Digit) :
    run0 p 7 (E (false::L) ([false,true,true,false]++enc ds)) = some (E (false::(M++L)) (suffix ds)) := by
  cases ds with
  | nil => rfl
  | cons d ds => cases d <;> rfl

theorem carry (L : List Bool) (ds : List Digit) :
    run0 p 3 (E (false::L) (suffix (.d3::ds))) = some (E (false::(X++L)) (suffix ds)) := by
  cases ds with
  | nil => rfl
  | cons d ds => cases d <;> rfl

-- A noncarry digit directly at the frame, or at a transferred digit,
-- returns to A and writes the new digit.  The empty suffix appends digit2.
theorem frame0 (L R : List Bool) :
    run0 p 6 (E (false::(M++L)) (pair .d0++R)) = some (A (H++L) (P++digit .d1++R)) := rfl
theorem frame1 (L R : List Bool) :
    run0 p 8 (E (false::(M++L)) (pair .d1++R)) = some (A (H++L) (P++digit .d2++R)) := rfl
theorem frame2 (L R : List Bool) :
    run0 p 6 (E (false::(M++L)) (pair .d2++R)) = some (A (H++L) (P++digit .d3++R)) := rfl
theorem frameEnd (L : List Bool) :
    run0 p 8 (E (false::(M++L)) []) = some (A (H++L) (P++digit .d2)) := rfl

theorem block0 (L R : List Bool) :
    run0 p 4 (E (false::(X++L)) (pair .d0++R)) = some (A (H++L) (false::(digit .d1++R))) := rfl
theorem block1 (L R : List Bool) :
    run0 p 6 (E (false::(X++L)) (pair .d1++R)) = some (A (H++L) (false::(digit .d2++R))) := rfl
theorem block2 (L R : List Bool) :
    run0 p 4 (E (false::(X++L)) (pair .d2++R)) = some (A (H++L) (false::(digit .d3++R))) := rfl
theorem blockEnd (L : List Bool) :
    run0 p 6 (E (false::(X++L)) []) = some (A (H++L) (false::digit .d2)) := rfl

theorem frameBack (L R : List Bool) :
    run0 p 5 (A (H++M++L) R) = some (A (H++L) (P++J++R)) := rfl

theorem unwind (k : Nat) (L R : List Bool) :
    run0 p (3*k+5) (A (H++rep X k++(M++L)) (false::R)) = some (A (H++L) (rep P (k+2)++R)) := by
  have h := backSweep k (M++L) (false::R)
  have j := join0 h (frameBack L (rep Y k++false::R))
  have eq : P++J++(rep Y k++false::R) = rep P (k+2)++R := by
    rw [List.append_assoc,←List.append_assoc J,rot]
    simp only [List.append_assoc]
    rw [show J++false::R=P++R by rfl]
    rw [←List.append_assoc (rep P k),rep_snoc]
    rfl
  rw [eq] at j
  simpa only [List.append_assoc] using j

def pref (k : Nat) (L : List Bool) := false::(rep X k++M++L)

-- Resolve a carry run of any length: every traversed digit3 becomes digit0.
theorem stop (k : Nat) (L : List Bool) (ds : List Digit)
    (h : ∀ tail, ds ≠ .d3::tail) : ∃ t, 0<t ∧
    run0 p t (E (pref k L) (suffix ds)) = some (A (H++L) (rep P (k+1)++enc (inc ds))) := by
  cases ds with
  | nil =>
    cases k with
    | zero => exact ⟨8,by decide,frameEnd L⟩
    | succ k =>
      have j := join0 (blockEnd (rep X k++M++L)) (by simpa only [List.append_assoc] using unwind k L (digit .d2))
      exact ⟨6+(3*k+5),by omega,by simpa only [pref,suffix,rep,List.append_assoc,inc,enc,List.append_nil] using j⟩
  | cons d ds =>
    cases d with
    | d3 => exact False.elim (h ds rfl)
    | d0 =>
      cases k with
      | zero => exact ⟨6,by decide,frame0 L (enc ds)⟩
      | succ k =>
        have j := join0 (block0 (rep X k++M++L)) (by simpa only [List.append_assoc] using unwind k L (digit .d1++enc ds))
        exact ⟨4+(3*k+5),by omega,by simpa only [pref,suffix,rep,List.append_assoc,inc,enc] using j⟩
    | d1 =>
      cases k with
      | zero => exact ⟨8,by decide,frame1 L (enc ds)⟩
      | succ k =>
        have j := join0 (block1 (rep X k++M++L)) (by simpa only [List.append_assoc] using unwind k L (digit .d2++enc ds))
        exact ⟨6+(3*k+5),by omega,by simpa only [pref,suffix,rep,List.append_assoc,inc,enc] using j⟩
    | d2 =>
      cases k with
      | zero => exact ⟨6,by decide,frame2 L (enc ds)⟩
      | succ k =>
        have j := join0 (block2 (rep X k++M++L)) (by simpa only [List.append_assoc] using unwind k L (digit .d3++enc ds))
        exact ⟨4+(3*k+5),by omega,by simpa only [pref,suffix,rep,List.append_assoc,inc,enc] using j⟩

theorem scan (ds : List Digit) (k : Nat) (L : List Bool) : ∃ t, 0<t ∧
    run0 p t (E (pref k L) (suffix ds)) = some (A (H++L) (rep P (k+1)++enc (inc ds))) := by
  induction ds generalizing k with
  | nil => exact stop k L [] (by intro tail h; cases h)
  | cons d ds ih =>
    cases d with
    | d0 => exact stop k L (.d0::ds) (by intro tail h; cases h)
    | d1 => exact stop k L (.d1::ds) (by intro tail h; cases h)
    | d2 => exact stop k L (.d2::ds) (by intro tail h; cases h)
    | d3 =>
      obtain ⟨t,ht,hr⟩ := ih (k+1)
      have h := carry (rep X k++M++L) ds
      have h' : run0 p 3 (E (pref k L) (suffix (.d3::ds))) = some (E (pref (k+1) L) (suffix ds)) := by
        simpa only [pref,rep,List.append_assoc] using h
      have j := join0 h' hr
      refine ⟨3+t,by omega,?_⟩
      have eq : rep P (k+1+1)++enc (inc ds) = rep P (k+1)++enc (inc (.d3::ds)) := by
        have hh : rep P (k+1)++P = rep P (k+1+1) := rep_snoc P (k+1)
        rw [←hh,inc,enc,List.append_assoc]
        rfl
      rw [eq] at j
      exact j

theorem phase3 (n : Nat) (ds : List Digit) : ∃ t, 0<t ∧
    run0 p t (root n [false,true,true,false] ds) = some (root (n+1) H (inc ds)) := by
  have h := enter n ([false,true,true,false]++enc ds)
  have h' := prepare (rep X n++Z) ds
  obtain ⟨t,ht,hr⟩ := scan ds 0 (rep X n++Z)
  have j := join0 (join0 h h') hr
  have j' := join0 j (back n (rep P (0+1)++enc (inc ds)))
  refine ⟨3+3*n+7+t+(3*n+5),by omega,?_⟩
  have eq : rep P (n+1)++J++(rep P (0+1)++enc (inc ds)) = rep P (n+1+1)++H++enc (inc ds) := by
    have hh : rep P (n+1)++P = rep P (n+1+1) := rep_snoc P (n+1)
    rw [List.append_assoc,show J++(rep P (0+1)++enc (inc ds))=P++(H++enc (inc ds)) by rfl,←List.append_assoc,hh,List.append_assoc]
  rw [eq] at j'
  simpa only [root,List.append_assoc] using j' 

theorem growth (n : Nat) (ds : List Digit) : ∃ t, 0<t ∧
    run0 p t (root n H ds) = some (root (n+1) H (inc ds)) := by
  obtain ⟨a,ha,h1⟩ := phase1 n ds
  obtain ⟨b,hb,h2⟩ := phase2 n ds
  obtain ⟨c,hc,h3⟩ := phase3 n ds
  exact ⟨a+b+c,by omega,join0 (join0 h1 h2) h3⟩

def digits : Nat → List Digit
  | 0 => [.d2]
  | n+1 => inc (digits n)
def family (n : Nat) : Z0 := root n H (digits n)
theorem init : run0 p 22 (A [] []) = some (family 0) := rfl

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  let cost := fun n => Classical.choose (growth n (digits n))
  exact never_of_growth p family 22 cost init
    (fun n => (Classical.choose_spec (growth n (digits n))).1)
    (fun n => (Classical.choose_spec (growth n (digits n))).2) m hm

#print axioms never
#print axioms growth
#print axioms init
end BB6.Agent46Raw13Coupled6RFQuaternary
