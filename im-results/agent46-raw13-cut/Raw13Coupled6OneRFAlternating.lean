import SweepPumping
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled6OneRFAlternating
open BB6Coverage BB6Coverage.Agent31Pump

def p : PartialMachine := FAR.fromCodes [7,14,11,12,2,19,17,0,7,23,4,24]
abbrev A (l r : List Bool) : Z0 := ⟨0,l,r⟩
abbrev E (l r : List Bool) : Z0 := ⟨4,l,r⟩
abbrev P : List Bool := [false,true]
abbrev U : List Bool := [true,true]
abbrev B0 : List Bool := P
abbrev B1 : List Bool := [false,false]
inductive Digit | q0 | q1 | q2 | q3
inductive Terminal | t0 | t1 | t2 | t3
inductive Word | terminal (t : Terminal) | digit (b : Bool) (q : Digit) (w : Word)
def qcode : Digit → List Bool
  | .q0 => P | .q1 => [true,true] | .q2 => B1 | .q3 => [true,false]
def tcode : Terminal → List Bool
  | .t0 => [false,true,true]
  | .t1 => [false,true,false,false,false]
  | .t2 => [false,true,false,true,true]
  | .t3 => [false,true,false,false,true]
def enc : Word → List Bool
  | .terminal t => tcode t
  | .digit b q w => P++(if b then B1 else B0)++qcode q++enc w

-- The Boolean result indicates a return to A with no leading one.
def inc : Word → Bool × Word
  | .terminal .t0 => (true,.terminal .t1)
  | .terminal .t1 => (false,.terminal .t2)
  | .terminal .t2 => (false,.terminal .t3)
  | .terminal .t3 => (true,.digit false .q0 (.terminal .t0))
  | .digit false q w => (false,.digit true q w)
  | .digit true .q0 w => (false,.digit false .q1 w)
  | .digit true .q1 w => (false,.digit false .q2 w)
  | .digit true .q2 w => (false,.digit false .q3 w)
  | .digit true .q3 w => ((inc w).1,.digit false .q0 (inc w).2)

def outLeft (phase : Bool) (L : List Bool) := if phase then L else true::L

theorem pair (L R : List Bool) : run0 p 2 (A (U++L) R) = some (A L (P++R)) := rfl
theorem sweep (n : Nat) (L R : List Bool) : run0 p (2*n) (A (rep U n++L) R) = some (A L (rep P n++R)) := by
  simpa only [List.nil_append] using sweepL p 0 [] [] U P 2 (by intro L R; exact pair L R) n L R

theorem scan (w : Word) (L : List Bool) : ∃ t, 0<t ∧ run0 p t (E (false::L) (enc w)) = some (A (outLeft (inc w).1 L) (enc (inc w).2)) := by
  induction w generalizing L with
  | terminal t =>
    cases t with
    | t0 =>
      have h : run0 p 7 (E (false::L) (tcode .t0)) = some (A (rep U 1++L) [false,false,false]) := rfl
      exact ⟨9,by decide,join0 h (sweep 1 L [false,false,false])⟩
    | t1 =>
      have h : run0 p 6 (E (false::L) (tcode .t1)) = some (A (rep U 2++true::L) [true]) := rfl
      exact ⟨10,by decide,join0 h (sweep 2 (true::L) [true])⟩
    | t2 =>
      have h : run0 p 6 (E (false::L) (tcode .t2)) = some (A (rep U 1++true::L) [false,false,true]) := rfl
      exact ⟨8,by decide,join0 h (sweep 1 (true::L) [false,false,true])⟩
    | t3 =>
      have h : run0 p 9 (E (false::L) (tcode .t3)) = some (A (rep U 4++L) [true]) := rfl
      exact ⟨17,by decide,join0 h (sweep 4 L [true])⟩
  | digit b q w ih =>
    cases b with
    | false =>
      have h : run0 p 6 (E (false::L) (enc (.digit false q w))) = some (A (rep U 1++true::L) (B1++qcode q++enc w)) := by cases q <;> rfl
      exact ⟨8,by decide,join0 h (sweep 1 (true::L) (B1++qcode q++enc w))⟩
    | true =>
      cases q with
      | q0 =>
        have h : run0 p 6 (E (false::L) (enc (.digit true .q0 w))) = some (A (rep U 2++true::L) (qcode .q1++enc w)) := rfl
        exact ⟨10,by decide,join0 h (sweep 2 (true::L) (qcode .q1++enc w))⟩
      | q1 =>
        have h : run0 p 10 (E (false::L) (enc (.digit true .q1 w))) = some (A (rep U 2++true::L) (qcode .q2++enc w)) := by
          cases w with
          | terminal t => cases t <;> rfl
          | digit b q w => cases b <;> cases q <;> rfl
        exact ⟨14,by decide,join0 h (sweep 2 (true::L) (qcode .q2++enc w))⟩
      | q2 =>
        have h : run0 p 6 (E (false::L) (enc (.digit true .q2 w))) = some (A (rep U 2++true::L) (qcode .q3++enc w)) := rfl
        exact ⟨10,by decide,join0 h (sweep 2 (true::L) (qcode .q3++enc w))⟩
      | q3 =>
        have h : run0 p 6 (E (false::L) (enc (.digit true .q3 w))) = some (E (false::(rep U 3++L)) (enc w)) := rfl
        obtain ⟨t,ht,hr⟩ := ih (rep U 3++L)
        have hl : outLeft (inc w).1 (rep U 3++L) = rep U 3++outLeft (inc w).1 L := by
          cases hb : (inc w).1 <;> rfl
        rw [hl] at hr
        exact ⟨6+t+6,by omega,join0 (join0 h hr) (sweep 3 (outLeft (inc w).1 L) (enc (inc w).2))⟩

structure Counter where
  b : Bool
  q : Digit
  w : Word

def root (x : Counter) : Z0 := A [true,false] (enc (.digit x.b x.q x.w))
def next (x : Counter) : Counter :=
  match x.b,x.q with
  | false,q => ⟨true,q,x.w⟩
  | true,.q0 => ⟨false,.q1,x.w⟩
  | true,.q1 => ⟨false,.q2,x.w⟩
  | true,.q2 => ⟨false,.q3,x.w⟩
  | true,.q3 => ⟨false,if (inc x.w).1 then .q1 else .q0,(inc x.w).2⟩

theorem enter (b : Bool) (q : Digit) (w : Word) : run0 p 6 (root ⟨b,q,w⟩) = some (E [false,false] (enc (.digit b q w))) := rfl
theorem restart (w : Word) : run0 p 24 (A [false] (enc (.digit false .q0 w))) = some (root ⟨false,.q1,w⟩) := rfl

theorem growth (x : Counter) : ∃ t, 0<t ∧ run0 p t (root x) = some (root (next x)) := by
  obtain ⟨b,q,w⟩ := x
  obtain ⟨t,ht,hr⟩ := scan (.digit b q w) [false]
  have h := join0 (enter b q w) hr
  cases b with
  | false => exact ⟨6+t,by omega,h⟩
  | true =>
    cases q with
    | q0 => exact ⟨6+t,by omega,h⟩
    | q1 => exact ⟨6+t,by omega,h⟩
    | q2 => exact ⟨6+t,by omega,h⟩
    | q3 =>
      cases hp : (inc w).1 with
      | false => exact ⟨6+t,by omega,by simpa [inc,outLeft,next,root,hp] using h⟩
      | true =>
        have h' : run0 p (6+t) (root ⟨true,.q3,w⟩) = some (A [false] (enc (.digit false .q0 (inc w).2))) := by
          simpa only [inc,outLeft,hp,ite_true] using h
        exact ⟨6+t+24,by omega,by simpa [next,hp] using join0 h' (restart (inc w).2)⟩

def trajectory : Nat → Counter
  | 0 => ⟨false,.q1,.terminal .t0⟩
  | n+1 => next (trajectory n)
def family (n : Nat) := root (trajectory n)
theorem init : run0 p 85 (A [] []) = some (family 0) := rfl

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  let cost := fun n => Classical.choose (growth (trajectory n))
  exact never_of_growth p family 85 cost init
    (fun n => (Classical.choose_spec (growth (trajectory n))).1)
    (fun n => (Classical.choose_spec (growth (trajectory n))).2) m hm

#print axioms never
#print axioms growth
#print axioms init
end BB6.Agent46Raw13Coupled6OneRFAlternating
