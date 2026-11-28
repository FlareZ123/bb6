import SweepPumping
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled6OneRFPrefix
open BB6Coverage BB6Coverage.Agent31Pump

def p : PartialMachine := FAR.fromCodes [7,14,11,8,2,19,5,0,1,23,11,24]
abbrev A (l r : List Bool) : Z0 := ⟨0,l,r⟩
abbrev E (l r : List Bool) : Z0 := ⟨4,l,r⟩
abbrev P : List Bool := [true,false]
abbrev U : List Bool := [true,true]
abbrev Y : List Bool := [false,true]
abbrev D0 : List Bool := rep Y 3
abbrev D1 : List Bool := [false,true,true,false,false,true]
abbrev D2 : List Bool := [false,true,false,true,true,true]
abbrev D3 : List Bool := [false,true,true,false,true,true]
abbrev T0 : List Bool := [false,true,false,true,true]
abbrev T1 : List Bool := [false,true,true,false,true]
inductive Digit | d0 | d1 | d2 | d3
inductive Word | end0 | end1 | digit (d : Digit) (tail : Word)
def code : Digit → List Bool
  | .d0 => D0 | .d1 => D1 | .d2 => D2 | .d3 => D3
def enc : Word → List Bool
  | .end0 => T0 | .end1 => T1
  | .digit d w => code d ++ enc w
def inc : Word → Word
  | .end0 => .end1 | .end1 => .digit .d0 .end0
  | .digit .d0 w => .digit .d1 w
  | .digit .d1 w => .digit .d2 w
  | .digit .d2 w => .digit .d3 w
  | .digit .d3 w => .digit .d0 (inc w)

theorem pair (L R : List Bool) : run0 p 2 (A (U++L) R) = some (A L (Y++R)) := rfl
theorem unwind (L R : List Bool) : run0 p 6 (A (rep U 3++L) R) = some (A L (D0++R)) := by
  simpa only [List.nil_append] using sweepL p 0 [] [] U Y 2 (by intro L R; exact pair L R) 3 L R

theorem carry (w : Word) (L : List Bool) : ∃ t, 0<t ∧
    run0 p t (E (true::L) (enc w)) = some (A (true::L) (enc (inc w))) := by
  induction w generalizing L with
  | end0 => exact ⟨10,by decide,rfl⟩
  | end1 =>
    have h : run0 p 22 (E (true::L) T1) = some (A (rep U 3++true::L) T0) := rfl
    exact ⟨28,by decide,join0 h (unwind (true::L) T0)⟩
  | digit d w ih =>
    cases d with
    | d0 => exact ⟨10,by decide,rfl⟩
    | d1 => exact ⟨10,by decide,rfl⟩
    | d2 => exact ⟨10,by decide,rfl⟩
    | d3 =>
      have h : run0 p 6 (E (true::L) (D3++enc w)) = some (E (true::(rep U 3++L)) (enc w)) := rfl
      obtain ⟨t,ht,hr⟩ := ih (rep U 3++L)
      have he : true::(rep U 3++L) = rep U 3++true::L := rfl
      rw [he] at hr
      exact ⟨6+t+6,by omega,join0 (join0 h hr) (unwind (true::L) (enc (inc w)))⟩

theorem increment (w : Word) (L : List Bool) : ∃ t, 0<t ∧
    run0 p t (A (false::false::L) (enc w)) = some (A (P++L) (enc (inc w))) := by
  cases w with
  | end0 => exact ⟨10,by decide,rfl⟩
  | end1 => exact ⟨28,by decide,rfl⟩
  | digit d w =>
    cases d with
    | d0 => exact ⟨10,by decide,rfl⟩
    | d1 => exact ⟨10,by decide,rfl⟩
    | d2 => exact ⟨10,by decide,rfl⟩
    | d3 =>
      have h : run0 p 6 (A (false::false::L) (D3++enc w)) = some (E (true::(rep U 3++false::L)) (enc w)) := rfl
      obtain ⟨t,ht,hr⟩ := carry w (rep U 3++false::L)
      have he : true::(rep U 3++false::L) = rep U 3++P++L := rfl
      rw [he] at hr
      exact ⟨6+t+6,by omega,join0 (join0 h hr) (unwind (P++L) (enc (inc w)))⟩

theorem enter0 (R : List Bool) : run0 p 4 (A [] (P++R)) = some (A [false,false,true] R) := rfl
theorem enter1 (L R : List Bool) : run0 p 4 (A ([false,false]++L) (P++R)) = some (A ([false,false]++P++L) R) := rfl
theorem exit1 (L R : List Bool) : run0 p 4 (A (P++L) R) = some (A L (P++R)) := rfl
theorem exit0 (R : List Bool) : run0 p 4 (A [true] R) = some (A [] (P++R)) := rfl

def root (n : Nat) (w : Word) : Z0 := A [] (rep P (n+1)++enc w)
theorem growth (n : Nat) (w : Word) : ∃ t, 0<t ∧ run0 p t (root n w) = some (root (n+1) (inc w)) := by
  have h0 := enter0 (rep P n++enc w)
  have h1 := sweepR p 0 [false,false] [] P P 4 (by intro L R; exact enter1 L R) n [true] (enc w)
  have h1' : run0 p (4*n) (A [false,false,true] (rep P n++enc w)) = some (A (false::false::(rep P n++[true])) (enc w)) := by
    simpa only [List.nil_append,List.append_assoc,List.cons_append,List.singleton_append] using h1
  obtain ⟨t,ht,hr⟩ := increment w (rep P n++[true])
  have h2 := sweepL p 0 [] [] P P 4 (by intro L R; exact exit1 L R) (n+1) [true] (enc (inc w))
  have h2' : run0 p (4*(n+1)) (A (P++(rep P n++[true])) (enc (inc w))) = some (A [true] (rep P (n+1)++enc (inc w))) := by
    simpa only [List.nil_append,rep,List.append_assoc] using h2
  have h3 := exit0 (rep P (n+1)++enc (inc w))
  refine ⟨4+4*n+t+4*(n+1)+4,by omega,?_⟩
  simpa only [root,rep,List.append_assoc] using join0 (join0 (join0 (join0 h0 h1') hr) h2') h3

def trajectory : Nat → Word
  | 0 => .end0
  | n+1 => inc (trajectory n)
def family (n : Nat) := root n (trajectory n)
theorem init : run0 p 19 (A [] []) = some (family 0) := rfl

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  let cost := fun n => Classical.choose (growth n (trajectory n))
  exact never_of_growth p family 19 cost init
    (fun n => (Classical.choose_spec (growth n (trajectory n))).1)
    (fun n => (Classical.choose_spec (growth n (trajectory n))).2) m hm

#print axioms never
#print axioms growth
#print axioms init
end BB6.Agent46Raw13Coupled6OneRFPrefix
