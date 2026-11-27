import JCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace F197.MixedCarry
open JCarry

def inc (r : Tape) : Tape := cons true r
def s : Tape → Tape := pre [true,true,true,true,true,false,false,false]
def q (l : Tape) := t (a (t l))
inductive Token where | at | tt | p | q deriving DecidableEq

def input : Token → Tape → Tape
  | .at => fun l => a (t l)
  | .tt => fun l => t (t l)
  | .p => JCarry.p
  | .q => q

def push : Token → Tape → Tape
  | .at => tau
  | .tt => fun r => tau (a r)
  | .p => fun r => u (inc r)
  | .q => fun r => u (c r)

def flag : Token → Bool
  | .at | .p => false
  | .tt | .q => true

def dcode (v : Bool) (r : Tape) := if v then c r else inc r

def emit : Token → Bool → Tape → Tape
  | .at, v => h v
  | .tt, v => h v
  | .p, v => fun l => if v then a (p l) else p l
  | .q, v => fun l => if v then a (p l) else p l

def sc : Token → Nat
  | .at => 8 | .tt => 18 | .p => 36 | .q => 46

def dc (k : Token) (v : Bool) : Nat :=
  (match k with | .at | .tt => 60 | .p | .q => 32) + 4 * bit v

theorem consume (k : Token) (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run (sc k) (b (input k l) r) = some (b l (push k r)) := by
  cases k
  · exact scanA l r
  · exact scanT l r
  · rw [← decompose_bit l true hl, ← decompose_bit r true hr]; rfl
  · rw [← decompose_bit l true hl, ← decompose_bit r true hr]; rfl

theorem terminal (v : Bool) (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run (47 + 10 * bit v) (b (src v [] l) r) = some (b (j l) (x (dcode v r))) := by
  cases v <;> rw [← decompose_bit l true hl, ← decompose_bit r true hr] <;> rfl

theorem unpush (k : Token) (v : Bool) (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run (dc k v) (b (j l) (x (dcode v (push k r)))) =
    some (b (j (emit k v l)) (x (dcode (flag k) r))) := by
  cases k <;> cases v <;> rw [← decompose_bit l true hl, ← decompose_bit r true hr] <;> rfl

theorem finish (v : Bool) (l : Tape) (hl : l 0 = true) :
    run (27 + 4 * bit v) (b (j l) (x (dcode v e))) = some (b (a (h v l)) e) := by
  cases v <;> rw [← decompose_bit l true hl] <;> rfl

def inputs : List Token → Tape → Tape
  | [], l => l
  | k::ks, l => input k (inputs ks l)

def firstFlag (ks : List Token) (v : Bool) : Bool :=
  match ks with | [] => v | k::_ => flag k

def outputs : List Token → Bool → Tape → Tape
  | [], _, l => l
  | k::ks, v, l => emit k (firstFlag ks v) (outputs ks v l)

def midCost : List Token → Bool → Nat
  | [], v => 47 + 10 * bit v
  | k::ks, v => sc k + midCost ks v + dc k (firstFlag ks v)

theorem inputs_first (ks : List Token) (l : Tape) (hl : l 0 = true) : inputs ks l 0 = true := by
  cases ks with
  | nil => exact hl
  | cons k ks => cases k <;> rfl

theorem outputs_first (ks : List Token) (v : Bool) (l : Tape) (hl : l 0 = true) : outputs ks v l 0 = true := by
  cases ks with
  | nil => exact hl
  | cons k ks => cases k <;> cases hv : firstFlag ks v <;> simp [outputs, emit, hv, h, a, p, t, pre, cons]

theorem pushed_first (k : Token) (r : Tape) : push k r 0 = true := by
  cases k <;> rfl

theorem sandwich (ks : List Token) (v : Bool) (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run (midCost ks v) (b (inputs ks (src v [] l)) r) =
    some (b (j (outputs ks v l)) (x (dcode (firstFlag ks v) r))) := by
  induction ks generalizing r with
  | nil => exact terminal v l r hl hr
  | cons k ks ih =>
      have ht : src v [] l 0 = true := by cases v <;> rfl
      change run (sc k + midCost ks v + dc k (firstFlag ks v))
        (b (input k (inputs ks (src v [] l))) r) = _
      rw [run_add, run_add, consume k _ r (inputs_first ks _ ht) hr]
      simp only [Option.bind_some]
      rw [ih (push k r) (pushed_first k r)]
      simp only [Option.bind_some]
      exact unpush k (firstFlag ks v) (outputs ks v l) r (outputs_first ks v l hl) hr

def countFlags : List Token → Nat
  | [] => 0
  | k::ks => bit (flag k) + countFlags ks

theorem midCost_formula (ks : List Token) (v : Bool) :
    midCost ks v + 4 * bit (firstFlag ks v) =
    47 + 68 * ks.length + 14 * (countFlags ks + bit v) := by
  induction ks with
  | nil => simp [midCost, firstFlag, countFlags]; omega
  | cons k ks ih =>
      cases k <;> simp [midCost, sc, dc, flag, firstFlag, countFlags, bit] at * <;> omega

theorem family (ks : List Token) (v : Bool) (l : Tape) (hl : l 0 = true) :
    run (74 + 68 * ks.length + 14 * (countFlags ks + bit v))
      (b (inputs ks (src v [] l)) e) =
    some (b (a (h (firstFlag ks v) (outputs ks v l))) e) := by
  have hc := midCost_formula ks v
  rw [show 74 + 68 * ks.length + 14 * (countFlags ks + bit v) = midCost ks v + (27 + 4 * bit (firstFlag ks v)) by omega]
  rw [run_add, sandwich ks v l e hl (by rfl)]
  simp only [Option.bind_some]
  exact finish (firstFlag ks v) (outputs ks v l) (outputs_first ks v l hl)

theorem finishJ (v : Bool) (l : Tape) (hl : l 0 = true) :
    run (91 + 4 * bit v) (b (j l) (x (dcode v (tau two)))) = some (b (t (p (h v l))) e) := by
  cases v <;> rw [← decompose_bit l true hl] <;> rfl

theorem familyJ (ks : List Token) (v : Bool) (l y : Tape) (hl : l 0 = true) (hy : y 0 = true)
    (he : t y = inputs ks (src v [] l)) :
    run (209 + 68 * ks.length + 14 * (countFlags ks + bit v))
      (b (t (t (j y))) e) =
    some (b (t (p (h (firstFlag ks v) (outputs ks v l)))) e) := by
  have hc := midCost_formula ks v
  rw [show 209 + 68 * ks.length + 14 * (countFlags ks + bit v) = 71 + midCost ks v + (91 + 4 * bit (firstFlag ks v)) by omega]
  rw [run_add, run_add, enter y hy]
  simp only [Option.bind_some]
  rw [he, sandwich ks v l (tau two) hl (by rfl)]
  simp only [Option.bind_some]
  exact finishJ (firstFlag ks v) (outputs ks v l) (outputs_first ks v l hl)

#print axioms consume
#print axioms terminal
#print axioms unpush
#print axioms finish
#print axioms sandwich
#print axioms family
#print axioms familyJ
end F197.MixedCarry
