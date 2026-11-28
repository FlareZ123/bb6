import PrefixP
set_option maxRecDepth 100000
set_option maxHeartbeats 500000
namespace F197.MixedCarry
open JCarry

abbrev Word := List Bool -- false = A, true = T

def tapeOf : Word → Tape → Tape
  | [], l => l
  | c::cs,l => if c then t (tapeOf cs l) else a (tapeOf cs l)

theorem tapeOf_append (w z : Word) (l : Tape) :
    tapeOf (w++z) l = tapeOf w (tapeOf z l) := by
  induction w with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [tapeOf, ih]

theorem tapeOf_first (w : Word) (l : Tape) (hl : l 0 = true) : tapeOf w l 0 = true := by
  cases w with
  | nil => exact hl
  | cons c cs => cases c <;> rfl

def tokenIn : Token → Word
  | .at => [false,true]
  | .tt => [true,true]
  | .p => [false,false,true]
  | .q => [true,false,true]

def tokenOut : Token → Bool → Word
  | .at,v | .tt,v => if v then [false,false,true] else [false,true]
  | .p,v | .q,v => if v then [false,false,false,true] else [false,false,true]

def wordIn : List Token → Bool → Word
  | [],v => [v,false,false]
  | k::ks,v => tokenIn k ++ wordIn ks v

def wordOutAux : List Token → Bool → Word
  | [],_ => []
  | k::ks,v => tokenOut k (firstFlag ks v) ++ wordOutAux ks v

def wordOut (ks : List Token) (v : Bool) : Word :=
  (if firstFlag ks v then [false,false,false,true] else [false,false,true]) ++ wordOutAux ks v

theorem wordIn_eq (ks : List Token) (v : Bool) (l : Tape) :
    tapeOf (wordIn ks v) l = inputs ks (src v [] l) := by
  induction ks with
  | nil => cases v <;> rfl
  | cons k ks ih =>
    rw [wordIn, tapeOf_append, ih]
    cases k <;> rfl

theorem wordOutAux_eq (ks : List Token) (v : Bool) (l : Tape) :
    tapeOf (wordOutAux ks v) l = outputs ks v l := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    rw [wordOutAux, tapeOf_append, ih]
    cases k <;> cases hv : firstFlag ks v <;> simp [tokenOut, hv, outputs, emit, tapeOf, h, p, a, t]

theorem wordOut_eq (ks : List Token) (v : Bool) (l : Tape) :
    tapeOf (wordOut ks v) l = a (h (firstFlag ks v) (outputs ks v l)) := by
  rw [wordOut, tapeOf_append, wordOutAux_eq]
  cases firstFlag ks v <;> rfl

def Pword : Word := [false,false,true]
def pwords (n : Nat) : Word := (List.replicate n Pword).flatten

theorem leadP_add (n k : Nat) (l : Tape) : leadP (n+k) l = leadP n (leadP k l) := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih => exact ih (p l)

theorem pwords_eq (n : Nat) (l : Tape) : tapeOf (pwords n) l = leadP n l := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change tapeOf (Pword ++ pwords n) l = leadP n (p l)
    rw [tapeOf_append, ih, leadP_comm]
    rfl

def ruleCost (ks : List Token) (v : Bool) : Nat := 74 + 68*ks.length + 14*(countFlags ks+bit v)

/-- Each certificate row proves a finite prefix identity, leaving the arbitrary
    physical tail unchanged. d counts newly created leading P blocks. -/
structure Row where
  tokens : List Token
  terminal : Bool
  rest : Word
  delta : Nat
  next : Word

def rowOK (w : Word) (r : Row) : Bool :=
  (w == wordIn r.tokens r.terminal ++ r.rest) &&
  (wordOut r.tokens r.terminal ++ r.rest == pwords r.delta ++ r.next)

theorem row_sound (w : Word) (r : Row) (hok : rowOK w r = true)
    (n : Nat) (l : Tape) (hl : l 0 = true) :
    run (68*n + ruleCost r.tokens r.terminal) (b (leadP n (tapeOf w l)) e) =
      some (b (leadP (n+r.delta) (tapeOf r.next l)) e) := by
  have h := Bool.and_eq_true_iff.mp hok
  have h1 := beq_iff_eq.mp h.1
  have h2 := beq_iff_eq.mp h.2
  have H := familyP n r.tokens r.terminal (tapeOf r.rest l) (tapeOf_first _ l hl)
  rw [← wordIn_eq, ← wordOut_eq, ← tapeOf_append, ← tapeOf_append, ← h1, h2, tapeOf_append, pwords_eq, ← leadP_add] at H
  exact H

def certOK : Word → List Row → Bool
  | _,[] => true
  | w,r::rs => rowOK w r && certOK r.next rs

def certEnd : Word → List Row → Word
  | w,[] => w
  | _,r::rs => certEnd r.next rs

def certDelta : List Row → Nat
  | [] => 0
  | r::rs => r.delta + certDelta rs

def certCost : List Row → Nat
  | [] => 0
  | r::rs => ruleCost r.tokens r.terminal + 68*r.delta*rs.length + certCost rs

theorem cert_sound (w : Word) (rs : List Row) (hok : certOK w rs = true)
    (n : Nat) (l : Tape) (hl : l 0 = true) :
    run (68*n*rs.length + certCost rs) (b (leadP n (tapeOf w l)) e) =
      some (b (leadP (n+certDelta rs) (tapeOf (certEnd w rs) l)) e) := by
  induction rs generalizing w n with
  | nil => simp [certDelta, certEnd, certCost, run]
  | cons r rs ih =>
    have h := Bool.and_eq_true_iff.mp hok
    have hc : 68*n*(r::rs).length + certCost (r::rs) =
      (68*n + ruleCost r.tokens r.terminal) + (68*(n+r.delta)*rs.length + certCost rs) := by
      simp [certCost, List.length_cons, Nat.mul_succ, Nat.add_mul, Nat.mul_add]
      omega
    rw [hc, run_add, row_sound w r h.1 n l hl]
    simp only [Option.bind_some]
    simpa only [certDelta, certEnd, Nat.add_assoc] using ih r.next h.2 (n+r.delta)

#print axioms row_sound
#print axioms cert_sound
end F197.MixedCarry
