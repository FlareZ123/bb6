import CarryMacro
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Raw110Word
open BB6BlockFAR
open BB6Carry hiding render
abbrev render := BB6Carry.render

def word (w : List Bool) : Ray := bits w blankRay

inductive Pair where | A | B | C | D
  deriving DecidableEq, Repr

def Pair.bits : Pair → List Bool
  | .A => [true,false]
  | .B => [false,true]
  | .C => [false,false]
  | .D => [true,true]
def flatten : List Pair → List Bool
  | [] => []
  | a::r => a.bits ++ flatten r

def pair (a b : Bool) : Pair := if a then (if b then .D else .A) else (if b then .B else .C)
def pairs : List Bool → List Pair
  | [] => []
  | [a] => [pair a false]
  | a::b::r => pair a b :: pairs r

theorem pair_bits (a b : Bool) : (pair a b).bits = [a,b] := by cases a <;> cases b <;> rfl

theorem bits_append (a b : List Bool) (r : Ray) : bits (a++b) r = bits a (bits b r) := by
  induction a with
  | nil => rfl
  | cons x a ih => simp only [List.cons_append,bits,ih]

theorem pairs_word (w : List Bool) : word (flatten (pairs w)) = word w := by
  match w with
  | [] => rfl
  | [a] => cases a <;> simp [pairs,flatten,pair,Pair.bits,word,bits,blank_cons]
  | a::b::r =>
    change bits ((pair a b).bits ++ flatten (pairs r)) blankRay = _
    rw [pair_bits,bits_append]
    change bits [a,b] (word (flatten (pairs r))) = bits [a,b] (word r)
    rw [pairs_word r]

structure State where
  l : List Bool
  r : List Pair
  deriving DecidableEq, Repr

def State.render (s : State) : Prim := BB6Carry.render .B s.l (word (flatten s.r))

/-- Finite exact sweeps, preserving the odd-alignment blank-end shift. -/
def cw : List Bool → List Bool → Nat × (List Bool × List Bool)
  | [],r => (3,[false],r)
  | false::l,r => (3,false::false::l,r)
  | true::l,r => let t := cw l (true::false::r); (2+t.1,t.2)
def fw (slow : Bool) : List Bool → List Bool → Nat × (List Bool × List Bool)
  | [],r => (4,[false],r)
  | false::l,r => let t := fw slow l (true::false::r); (2+t.1,t.2)
  | true::l,r => let t := cw l (false::r); ((if slow then 6 else 2)+t.1,t.2)

theorem join (slow : Bool) {a b c : Prim} {n k : Nat}
    (h : run (machine slow) n a = some b) (g : run (machine slow) k b = some c) :
    run (machine slow) (n+k) a = some c := by rw [run_add,h]; exact g

theorem cw_sound (slow : Bool) (l r : List Bool) :
    let t := cw l r
    run (machine slow) t.1 (render .C l (bits [true,false] (word r))) =
      some (render .B t.2.1 (word t.2.2)) := by
  induction l generalizing r with
  | nil => exact Cnil slow (word r)
  | cons a l ih =>
    cases a with
    | false => exact C01 slow l (word r)
    | true => exact join slow (C10 slow l (bits [true,false] (word r))) (ih (true::false::r))

theorem fw_sound (slow : Bool) (l r : List Bool) :
    let t := fw slow l r
    run (machine slow) t.1 (render .F l (cons false (word r))) =
      some (render .B t.2.1 (word t.2.2)) := by
  induction l generalizing r with
  | nil => exact Fnil slow (word r)
  | cons a l ih =>
    cases a with
    | false => exact join slow (F01 slow l (cons false (word r))) (ih (true::false::r))
    | true => exact join slow (F10 slow l (word r)) (cw_sound slow l (false::r))

inductive Outcome where
  | halt (moves : Nat)
  | next (moves : Nat) (s : State)
  deriving DecidableEq, Repr

def Outcome.prepend (k : Nat) : Outcome → Outcome
  | .halt n => .halt (k+n)
  | .next n s => .next (k+n) s

def Outcome.sound (slow : Bool) (x : Prim) : Outcome → Prop
  | .halt n => ∃ y, run (machine slow) n x = some y ∧ primStep (machine slow) y = none
  | .next n s => run (machine slow) n x = some s.render

theorem prepend_sound (slow : Bool) {x y : Prim} {k : Nat} {o : Outcome}
    (h : run (machine slow) k x = some y) (g : o.sound slow y) : (o.prepend k).sound slow x := by
  cases o with
  | halt n =>
    obtain ⟨z,hz,hf⟩ := g
    exact ⟨z,join slow h hz,hf⟩
  | next n s => exact join slow h g

def finish (k : Nat) (t : Nat × (List Bool × List Bool)) : Outcome :=
  .next (k+t.1) ⟨t.2.1,pairs t.2.2⟩

theorem finish_sound (slow : Bool) {x : Prim} {k : Nat} {l r : List Bool}
    (h : run (machine slow) k x = some (render .F l (cons false (word r)))) :
    (finish k (fw slow l r)).sound slow x := by
  change run (machine slow) (k+(fw slow l r).1) x = some (render .B (fw slow l r).2.1 (word (flatten (pairs (fw slow l r).2.2))))
  rw [pairs_word]
  exact join slow h (fw_sound slow l r)

def bw (slow : Bool) : List Pair → List Bool → Outcome
  | [],l => finish 7 (fw slow l [false,true])
  | .A::r,l => (bw slow r (true::l)).prepend 2
  | .B::r,l => finish (if slow then 7 else 3) (fw slow l (false::flatten r))
  | .C::[],l => finish 7 (fw slow l [false,true])
  | .C::.A::r,l => (bw slow r (false::false::l)).prepend 4
  | .C::.B::r,l => finish 7 (fw slow l (false::true::true::flatten r))
  | .C::.C::r,l => finish 7 (fw slow l (false::true::false::flatten r))
  | .C::.D::r,l => finish 7 (fw slow l (true::false::false::flatten r))
  | .D::_,_ => .halt 1

theorem blank3 : bits [false,false,false] blankRay = blankRay := by simp [bits,blank_cons]

theorem bw_sound (slow : Bool) (w : List Pair) (l : List Bool) :
    (bw slow w l).sound slow (render .B l (word (flatten w))) := by
  match w with
  | [] =>
    have hb := B000 slow l blankRay
    rw [blank3] at hb
    exact finish_sound slow hb
  | .A::r => exact prepend_sound slow (B10 slow l (word (flatten r))) (bw_sound slow r (true::l))
  | .B::r => exact finish_sound slow (B01 slow l (word (flatten r)))
  | .C::[] =>
    have hb := B000 slow l blankRay
    rw [blank3] at hb
    have hc : word (flatten [.C]) = blankRay := by simp [word,flatten,Pair.bits,bits,blank_cons]
    rw [hc]
    exact finish_sound slow hb
  | .C::.A::r => exact prepend_sound slow (B0010 slow l (word (flatten r))) (bw_sound slow r (false::false::l))
  | .C::.B::r => exact finish_sound slow (B000 slow l (cons true (word (flatten r))))
  | .C::.C::r => exact finish_sound slow (B000 slow l (cons false (word (flatten r))))
  | .C::.D::r => exact finish_sound slow (B0011 slow l (word (flatten r)))
  | .D::r =>
    change ∃ y, run (machine slow) 1 (render .B l (word (flatten (.D::r)))) = some y ∧ primStep (machine slow) y = none
    cases slow <;> exact ⟨_,rfl,rfl⟩

def first : State := ⟨[true],[]⟩

def replay (slow : Bool) : Nat → State → Outcome
  | 0,s => .next 0 s
  | n+1,s => match bw slow s.r s.l with
    | .halt k => .halt k
    | .next k t => (replay slow n t).prepend k

theorem replay_sound (slow : Bool) (n : Nat) (s : State) : (replay slow n s).sound slow s.render := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have h := bw_sound slow s.r s.l
    change (bw slow s.r s.l).sound slow s.render at h
    unfold replay
    cases e : bw slow s.r s.l with
    | halt k => rw [e] at h; exact h
    | next k t => rw [e] at h; exact prepend_sound slow h (ih t)

theorem first_sound (slow : Bool) : run (machine slow) 1 primBlank = some first.render := BB6Carry.start slow

theorem checked_next (slow : Bool) (n k : Nat) (s t : State)
    (h : replay slow n s = .next k t) :
    run (machine slow) k s.render = some t.render := by
  have hs := replay_sound slow n s
  rw [h] at hs
  exact hs

theorem checked_halt (slow : Bool) (n k : Nat) (s : State)
    (h : replay slow n s = .halt k) :
    (Outcome.halt k).sound slow s.render := by
  have hs := replay_sound slow n s
  rw [h] at hs
  exact hs

#print axioms replay_sound
#print axioms first_sound
#print axioms checked_next
#print axioms checked_halt
end BB6Raw110Word
