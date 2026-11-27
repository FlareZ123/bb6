import Box33SourceBridge
import Box17AuditCore
import Box33D14Growth

namespace BB6.Agent13.Box33D17V22CarryFamily
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep cfg)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

inductive Kind where
  | m1 | m2 | m3 | m4 | m5 | m6 | m8 | m10
  deriving DecidableEq
inductive Mode where
  | a | c | x
  deriving DecidableEq

def step (v : Kind) (c : C9Pair.Config) : Option C9Pair.Config :=
  match v with
  | .m1 => match c.q,c.a with
    | .A,false => some (right .B true c)
    | .A,true => some (right .A false c)
    | .B,false => some (left .C true c)
    | .B,true => some (right .F true c)
    | .C,false => some (left .A false c)
    | .C,true => some (left .D false c)
    | .D,false => some (left .E false c)
    | .D,true => none
    | .E,false => some (right .F false c)
    | .E,true => some (left .C false c)
    | .F,false => some (left .E true c)
    | .F,true => some (right .C true c)
  | .m2 => match c.q,c.a with
    | .A,false => some (right .B true c)
    | .A,true => none
    | .B,false => some (left .C true c)
    | .B,true => some (right .F true c)
    | .C,false => some (left .A false c)
    | .C,true => some (left .D false c)
    | .D,false => some (left .E false c)
    | .D,true => some (left .E false c)
    | .E,false => some (right .F false c)
    | .E,true => some (left .E false c)
    | .F,false => some (left .E true c)
    | .F,true => some (right .A true c)
  | .m3 => match c.q,c.a with
    | .A,false => some (right .B true c)
    | .A,true => none
    | .B,false => some (left .C true c)
    | .B,true => some (right .F true c)
    | .C,false => some (left .A false c)
    | .C,true => some (left .D false c)
    | .D,false => some (left .E false c)
    | .D,true => some (right .D true c)
    | .E,false => some (right .F false c)
    | .E,true => some (left .E false c)
    | .F,false => some (left .E true c)
    | .F,true => some (right .A true c)
  | .m4 => match c.q,c.a with
    | .A,false => some (right .B true c)
    | .A,true => none
    | .B,false => some (left .C true c)
    | .B,true => some (right .F true c)
    | .C,false => some (left .A false c)
    | .C,true => some (left .D false c)
    | .D,false => some (left .E false c)
    | .D,true => some (left .E false c)
    | .E,false => some (right .F false c)
    | .E,true => some (left .C false c)
    | .F,false => some (left .E true c)
    | .F,true => some (right .A true c)
  | .m5 => match c.q,c.a with
    | .A,false => some (right .B true c)
    | .A,true => none
    | .B,false => some (left .C true c)
    | .B,true => some (right .F true c)
    | .C,false => some (left .A false c)
    | .C,true => some (left .D false c)
    | .D,false => some (left .E false c)
    | .D,true => some (right .D true c)
    | .E,false => some (right .F false c)
    | .E,true => some (left .D false c)
    | .F,false => some (left .E true c)
    | .F,true => some (right .A false c)
  | .m6 => match c.q,c.a with
    | .A,false => some (right .B true c)
    | .A,true => none
    | .B,false => some (left .C true c)
    | .B,true => some (right .F true c)
    | .C,false => some (left .A false c)
    | .C,true => some (left .D false c)
    | .D,false => some (left .E false c)
    | .D,true => some (left .D false c)
    | .E,false => some (right .F false c)
    | .E,true => some (left .D false c)
    | .F,false => some (left .E true c)
    | .F,true => some (right .A false c)
  | .m8 => match c.q,c.a with
    | .A,false => some (right .B true c)
    | .A,true => some (left .E true c)
    | .B,false => some (left .C true c)
    | .B,true => some (right .F true c)
    | .C,false => some (left .A false c)
    | .C,true => some (left .D false c)
    | .D,false => some (left .E false c)
    | .D,true => none
    | .E,false => some (right .F false c)
    | .E,true => some (left .C false c)
    | .F,false => some (right .C true c)
    | .F,true => some (right .A false c)
  | .m10 => match c.q,c.a with
    | .A,false => some (right .B true c)
    | .A,true => none
    | .B,false => some (left .C true c)
    | .B,true => some (right .F true c)
    | .C,false => some (left .A false c)
    | .C,true => some (left .D false c)
    | .D,false => some (left .E false c)
    | .D,true => some (left .E true c)
    | .E,false => some (right .F false c)
    | .E,true => some (left .C false c)
    | .F,false => some (right .A true c)
    | .F,true => some (left .E false c)

def run (v : Kind) : Nat → C9Pair.Config → Option C9Pair.Config
  | 0,c => some c
  | n+1,c => (step v c).bind (run v n)

theorem run_add (v : Kind) (m n : Nat) (c : C9Pair.Config) :
    run v (m+n) c = (run v m c).bind (run v n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => rw [Nat.succ_add]; simp only [run]; cases h : step v c <;> simp [ih]

def oneBase : Kind → Bool
  | .m2 | .m3 | .m4 | .m10 => true
  | _ => false
def base (v : Kind) : Stream := if oneBase v then push true z else z
def block (v : Kind) : List Bool := [oneBase v,true,true]
abbrev stack (v : Kind) (k : Nat) := rep (block v) k (base v)

def sweepQ : Kind → Q
  | .m2 | .m3 | .m5 => .E
  | .m6 => .D
  | _ => .C
def modeQ (v : Kind) : Mode → Q
  | .a => .A
  | .c => .C
  | .x => sweepQ v
def scan : Mode → Bool
  | .a => false
  | _ => true
def sweepMode (x : Bool) : Mode := if x then .x else .c

def digitBits (d : Bool × Bool) (r : Stream) : Stream := word [d.1,d.2,false] r
def digits : List (Bool × Bool) → Stream
  | [] => z
  | d::w => digitBits d (digits w)
def phase (v : Kind) (s : Mode) (k : Nat) (w : List (Bool × Bool)) : C9Pair.Config :=
  cfg (modeQ v s) (stack v k) (push (scan s) (digits w))

def carry (v : Kind) (a b : Bool) : Bool :=
  if v = .m10 then a && !b else a && b
def inc (a b : Bool) : Bool × Bool := (!a,if a then !b else b)
def digitMode (v : Kind) (a b : Bool) : Mode :=
  if carry v a b then .a else if a && !b then .x else .c

def digitCost (v : Kind) (a b : Bool) : Nat :=
  if !a then 2
  else if b then
    match v with | .m1 => 5 | .m10 => 4 | _ => 3
  else
    match v with | .m5 | .m8 => 6 | .m10 => 3 | _ => 4

def popCost (v : Kind) (x : Bool) : Nat :=
  match v with
  | .m5 => 5
  | .m3 => if x then 3 else 5
  | _ => 3
def turnCost (v : Kind) (x : Bool) : Nat :=
  match v with
  | .m1 | .m8 => 8
  | .m3 => if x then 6 else 8
  | _ => 6
def popDigit (v : Kind) : Bool × Bool :=
  if v = .m10 then (false,true) else (false,false)

-- All the following equalities hold for arbitrary left/right tails, not just samples.
theorem digitMacro (v : Kind) (a b : Bool) (l r : Stream) :
    run v (digitCost v a b) (cfg .A l (push false (digitBits (a,b) r))) =
      some (cfg (modeQ v (digitMode v a b))
        (if carry v a b then word (block v) l else l)
        (push (scan (digitMode v a b)) (if carry v a b then r else digitBits (inc a b) r))) := by
  cases v <;> cases a <;> cases b <;>
    simp [digitCost,carry,inc,digitMode,block,oneBase,modeQ,sweepQ,scan,digitBits,cfg,run,step,left,right,word]

theorem popMacro (v : Kind) (x : Bool) (l r : Stream) :
    run v (popCost v x) (cfg (modeQ v (sweepMode x)) (word (block v) l) (push true r)) =
      some (cfg (modeQ v .x) l (push true (digitBits (popDigit v) r))) := by
  cases v <;> cases x <;>
    simp [popCost,popDigit,sweepMode,block,oneBase,modeQ,sweepQ,digitBits,cfg,run,step,left,right,word]

theorem turnMacro (v : Kind) (x : Bool) (r : Stream) :
    run v (turnCost v x) (cfg (modeQ v (sweepMode x)) (base v) (push true r)) =
      some (cfg .A (base v) (push false r)) := by
  cases v <;> cases x <;>
    simp [turnCost,sweepMode,base,oneBase,modeQ,sweepQ,cfg,run,step,left,right,word]

theorem digitProgress (v : Kind) (a b : Bool) (k : Nat) (w : List (Bool × Bool)) :
    ∃ t : Nat, 0<t ∧ ∃ s' k' w', run v t (phase v .a k ((a,b)::w)) = some (phase v s' k' w') := by
  have he := digitMacro v a b (stack v k) (digits w)
  have ht : 0 < digitCost v a b := by cases v <;> cases a <;> cases b <;> decide
  cases hc : carry v a b with
  | false =>
    exact ⟨digitCost v a b,ht,digitMode v a b,k,inc a b::w,
      by simpa [phase,digits,modeQ,scan,hc] using he⟩
  | true =>
    exact ⟨digitCost v a b,ht,digitMode v a b,k+1,w,
      by simpa [phase,digits,modeQ,scan,hc,stack] using he⟩

theorem sweepProgress (v : Kind) (x : Bool) (k : Nat) (w : List (Bool × Bool)) :
    ∃ t : Nat, 0<t ∧ ∃ s' k' w', run v t (phase v (sweepMode x) k w) = some (phase v s' k' w') := by
  cases k with
  | zero =>
    exact ⟨turnCost v x,by cases v <;> cases x <;> decide,.a,0,w,
      by simpa [phase,stack,sweepMode,scan,modeQ] using turnMacro v x (digits w)⟩
  | succ k =>
    exact ⟨popCost v x,by cases v <;> cases x <;> decide,.x,k,popDigit v::w,
      by simpa [phase,stack,digits,sweepMode,scan] using popMacro v x (stack v k) (digits w)⟩

theorem progress (v : Kind) (s : Mode) (k : Nat) (w : List (Bool × Bool)) :
    ∃ t : Nat, 0<t ∧ ∃ s' k' w', run v t (phase v s k w) = some (phase v s' k' w') := by
  cases s with
  | a =>
    cases w with
    | nil =>
      have he : phase v .a k [] = phase v .a k [(false,false)] := by
        simp [phase,digits,digitBits,word]
      rw [he]
      exact digitProgress v false false k []
    | cons d w =>
      rcases d with ⟨a,b⟩
      exact digitProgress v a b k w
  | c => exact sweepProgress v false k w
  | x => exact sweepProgress v true k w

theorem never_phase (v : Kind) (n : Nat) (s : Mode) (k : Nat) (w : List (Bool × Bool)) :
    run v n (phase v s k w) ≠ none := by
  induction n using Nat.strongRecOn generalizing s k w with
  | ind n ih =>
    intro h
    obtain ⟨t,ht,s',k',w',he⟩ := progress v s k w
    by_cases hn : n≤t
    · rw [←show n+(t-n)=t by omega,run_add,h] at he
      contradiction
    · rw [←show t+(n-t)=n by omega,run_add,he,Option.bind_some] at h
      exact ih _ (by omega) s' k' w' h

def initCost (v : Kind) : Nat :=
  if oneBase v then if v = .m10 then 6 else 8 else 0
def initWord (v : Kind) : List (Bool × Bool) :=
  if oneBase v then [(true,false)] else []
def blank : C9Pair.Config := cfg .A z z
theorem init (v : Kind) : run v (initCost v) blank = some (phase v .a 0 (initWord v)) := by
  cases v <;> simp [initCost,initWord,oneBase,phase,stack,base,digits,digitBits,modeQ,scan,blank,cfg,run,step,left,right,word]

theorem never_blank (v : Kind) (n : Nat) : run v n blank ≠ none := by
  intro h
  by_cases hn : n≤initCost v
  · have he := init v
    rw [←show n+(initCost v-n)=initCost v by omega,run_add,h] at he
    contradiction
  · rw [←show initCost v+(n-initCost v)=n by omega,run_add,init,Option.bind_some] at h
    exact never_phase v _ .a 0 (initWord v) h

open BB6Coverage
open Box17 (index decode)
def codes : Kind → List (Fin 25)
  | .m1 => [8,2,11,24,1,13,17,0,22,9,19,12]
  | .m2 => [8,0,11,24,1,13,17,17,22,17,19,4]
  | .m3 => [8,0,11,24,1,13,17,16,22,17,19,4]
  | .m4 => [8,0,11,24,1,13,17,17,22,9,19,4]
  | .m5 => [8,0,11,24,1,13,17,16,22,13,19,2]
  | .m6 => [8,0,11,24,1,13,17,13,22,13,19,2]
  | .m8 => [8,19,11,24,1,13,17,0,22,9,12,2]
  | .m10 => [8,0,11,24,1,13,17,19,22,9,4,17]
def table (v : Kind) : Machine := fun s => decode ((codes v).getD (index s).val 0)
abbrev project := Box33Source.project false

theorem map_step (v : Kind) (c : BB6Coverage.Config) :
    (rawStep (table v) c).map project =
      match table v (readSlot c) with
      | none => none
      | some mv => some (if mv.right then C9Pair.right (Box33Source.q false mv.next) mv.write (project c)
                         else C9Pair.left (Box33Source.q false mv.next) mv.write (project c)) := by
  unfold rawStep
  cases ht : table v (readSlot c) with
  | none => rfl
  | some mv => simp only [Option.map_some,Box33Source.project_applyMove]

theorem project_step (v : Kind) (c : BB6Coverage.Config) :
    (rawStep (table v) c).map project = step v (project c) := by
  rw [map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  cases v <;> rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl

theorem project_run (v : Kind) (n : Nat) (c : BB6Coverage.Config) :
    (BB6Coverage.run (table v) n c).map project = run v n (project c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_add v n 1,←ih]
    simp only [BB6Coverage.run]
    cases ht : BB6Coverage.run (table v) n c with
    | none => rfl
    | some c' =>
      simp only [Option.bind_some,Option.map_some]
      simpa [run] using project_step v c'

theorem never (v : Kind) : NeverHalts (table v) := by
  intro n
  have he := project_run v n BB6Coverage.blank
  have hn : run v n (project BB6Coverage.blank) ≠ none := never_blank v n
  cases hr : BB6Coverage.run (table v) n BB6Coverage.blank with
  | none =>
    rw [hr] at he
    exact False.elim (hn he.symm)
  | some c => rfl

def partialTable (v : Kind) : PartialMachine := fun s => some (table v s)
theorem compatible_never (v : Kind) (m : Machine) (hm : compatible (partialTable v) m) : NeverHalts m := by
  have he : m = table v := funext fun s => hm s _ rfl
  rw [he]
  exact never v

#print axioms digitMacro
#print axioms popMacro
#print axioms compatible_never
end BB6.Agent13.Box33D17V22CarryFamily
