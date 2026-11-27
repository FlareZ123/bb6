import PackedAudit

/- Exact local-return proof for the two long A1 leaves of Raw139 E0=1LB.
   No finite simulation bound enters the local identities.  This source is
   a candidate until the pinned original dependency closure has compiled. -/
namespace BB6.Agent3OneLBReturn
open BB6Coverage BB6Coverage.FAR BB6Coverage.Agent13PackedZipper
open BB6.Agent3PackedAudit BB6.Agent31ThreeHole BB6.Agent13BlankDelay

abbrev Word := List Bool
abbrev z := false
abbrev o := true

def codes (slow : Bool) : List Nat :=
  [7,24,11,22,14,9,17,16,6,11,if slow then 15 else 16,0]
def parent (slow : Bool) : PartialMachine := fromCodes (codes slow)

-- Headless finite zipper, with implicit zeros at either end.  Left includes
-- the scanned bit, exactly as in the original packed zipper.
structure S where
  q : Fin 6
  l : Word
  r : Word
  deriving DecidableEq

def enc (s : S) : P := ⟨s.q,pack s.l,pack s.r⟩

def mvS (mv : Move) (s : S) : S :=
  if mv.right then
    ⟨mv.next,s.r.headD false::mv.write::s.l.tail,s.r.tail⟩
  else
    ⟨mv.next,s.l.tail,mv.write::s.r⟩

def stepS (slow : Bool) (s : S) : Option S :=
  ((parent slow (s.q,s.l.headD false)).bind id).map (fun mv => mvS mv s)

def runS (slow : Bool) : Nat → S → Option S
  | 0,s => some s
  | n+1,s => (stepS slow s).bind (runS slow n)

theorem enc_mv (mv : Move) (s : S) :
    enc (mvS mv s) = moveP mv (enc s) := by
  cases h : mv.right <;> simp [enc,mvS,moveP,h,pack,pack_head,pack_tail]

theorem enc_read (s : S) : readP (enc s) = (s.q,s.l.headD false) := by
  unfold readP enc
  rw [pack_head]
  cases s.l.headD false <;> rfl

theorem enc_step (slow : Bool) (s : S) :
    (stepS slow s).map enc = stepP (parent slow) (enc s) := by
  unfold stepS stepP
  rw [enc_read]
  cases h : (parent slow (s.q,s.l.headD false)).bind id with
  | none => rfl
  | some mv => simp [enc_mv]

theorem enc_run (slow : Bool) (n : Nat) (s : S) :
    (runS slow n s).map enc = runP (parent slow) n (enc s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [runS,runP,← enc_step]
    cases h : stepS slow s with
    | none => rfl
    | some t => exact ih t

theorem runS_add (slow : Bool) (n k : Nat) (s : S) :
    runS slow (n+k) s = (runS slow n s).bind (runS slow k) := by
  induction n generalizing s with
  | zero => simp [runS]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    simp only [runS]
    cases stepS slow s with
    | none => rfl
    | some t => exact ih t

theorem joinS {slow : Bool} {n k : Nat} {a b c : S}
    (h : runS slow n a = some b) (g : runS slow k b = some c) :
    runS slow (n+k) a = some c := by
  rw [runS_add,h]; exact g

-- E scans left, with a fixed zero immediately to its right.
-- C scans right, with left and right arguments exclusive/inclusive.
def E (l r : Word) : S := ⟨4,l,z::r⟩
def C (l r : Word) : S := ⟨2,r.headD z::l,r.tail⟩
def front (u : Word) : S := C u []
def gate (w r : Word) : S := ⟨0,o::w,[z,o,o,z]++r⟩

theorem blank_entry (slow : Bool) :
    runS slow 2 ⟨0,[],[]⟩ = some (front [o,o]) := by
  cases slow <;> rfl

theorem enter (slow : Bool) (w : Word) :
    runS slow 2 (front (o::w)) = some (E w [o]) := by
  cases slow <;> rfl

theorem e_b (slow : Bool) (w r : Word) :
    runS slow 3 (E (o::w) r) = some (E w (o::r)) := by
  cases slow <;> rfl

def aClock (slow : Bool) : Nat := if slow then 7 else 3

theorem e_a (slow : Bool) (w r : Word) :
    runS slow (aClock slow) (E ([z,o,z]++w) r) =
      some (E w ([o,o,z]++r)) := by
  cases slow <;> rfl

theorem turn00 (slow : Bool) (w r : Word) :
    runS slow 6 (E ([z,z]++w) r) = some (C ([o,z,o]++w) r) := by
  cases slow <;> rfl

theorem turn0110 (slow : Bool) (w r : Word) :
    runS slow 10 (E ([z,o,o,z]++w) r) = some (C ([o,z,z,o,o]++w) r) := by
  cases slow <;> rfl

theorem turn0111 (slow : Bool) (w r : Word) :
    runS slow 3 (E ([z,o,o,o]++w) r) = some (gate w r) := by
  cases slow <;> rfl

theorem c_b (slow : Bool) (l r : Word) :
    runS slow 1 (C l (o::r)) = some (C (z::l) r) := by
  cases slow <;> rfl

theorem c_a (slow : Bool) (l r : Word) :
    runS slow 5 (C l ([o,o,z]++r)) = some (C ([o,z,z]++l) r) := by
  cases slow <;> rfl

theorem finish (slow : Bool) (l : Word) :
    runS slow 4 (C l [o]) = some (front (o::z::l)) := by
  cases slow <;> rfl

inductive Tok where
  | a | b
  deriving DecidableEq, Repr

def token : Tok → Word
  | .a => [z,o,z]
  | .b => [o]

def code : Tok → Word
  | .a => [o,o,z]
  | .b => [o]

def phi : Tok → Word
  | .a => [o,z,z]
  | .b => [z]

def input : List Tok → Word → Word
  | [],w => w
  | t::ts,w => token t ++ input ts w

def codeRev : List Tok → Word → Word
  | [],r => r
  | t::ts,r => codeRev ts (code t ++ r)

def output : List Tok → Word → Word
  | [],l => l
  | t::ts,l => phi t ++ output ts l

def leftClock (slow : Bool) : List Tok → Nat
  | [] => 0
  | .a::ts => aClock slow + leftClock slow ts
  | .b::ts => 3 + leftClock slow ts

def rightClock : List Tok → Nat
  | [] => 0
  | .a::ts => rightClock ts + 5
  | .b::ts => rightClock ts + 1

theorem leftScan (slow : Bool) (ts : List Tok) (w r : Word) :
    runS slow (leftClock slow ts) (E (input ts w) r) =
      some (E w (codeRev ts r)) := by
  induction ts generalizing r with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | a => exact joinS (e_a slow (input ts w) r) (ih ([o,o,z]++r))
    | b => exact joinS (e_b slow (input ts w) r) (ih (o::r))

theorem rightScan (slow : Bool) (ts : List Tok) (l r : Word) :
    runS slow (rightClock ts) (C l (codeRev ts r)) =
      some (C (output ts l) r) := by
  induction ts generalizing r with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | a => exact joinS (ih ([o,o,z]++r)) (c_a slow (output ts l) r)
    | b => exact joinS (ih (o::r)) (c_b slow (output ts l) r)

def retClock (slow : Bool) (ts : List Tok) (extra : Nat) : Nat :=
  2 + leftClock slow ts + (6+extra) + rightClock ts + 4

def stopClock (slow : Bool) (ts : List Tok) : Nat :=
  2 + leftClock slow ts + 3

theorem return00 (slow : Bool) (ts : List Tok) (w : Word) :
    runS slow (retClock slow ts 0)
      (front (o::input ts ([z,z]++w))) =
      some (front (o::z::output ts ([o,z,o]++w))) := by
  exact joinS
    (joinS
      (joinS
        (joinS (enter slow (input ts ([z,z]++w))) (leftScan slow ts ([z,z]++w) [o]))
        (turn00 slow w (codeRev ts [o])))
      (rightScan slow ts ([o,z,o]++w) [o]))
    (finish slow (output ts ([o,z,o]++w)))

theorem return0110 (slow : Bool) (ts : List Tok) (w : Word) :
    runS slow (retClock slow ts 4)
      (front (o::input ts ([z,o,o,z]++w))) =
      some (front (o::z::output ts ([o,z,z,o,o]++w))) := by
  exact joinS
    (joinS
      (joinS
        (joinS (enter slow (input ts ([z,o,o,z]++w))) (leftScan slow ts ([z,o,o,z]++w) [o]))
        (turn0110 slow w (codeRev ts [o])))
      (rightScan slow ts ([o,z,z,o,o]++w) [o]))
    (finish slow (output ts ([o,z,z,o,o]++w)))

theorem return0111 (slow : Bool) (ts : List Tok) (w : Word) :
    runS slow (stopClock slow ts)
      (front (o::input ts ([z,o,o,o]++w))) =
      some (gate w (codeRev ts [o])) :=
  joinS
    (joinS (enter slow (input ts ([z,o,o,o]++w))) (leftScan slow ts ([z,o,o,o]++w) [o]))
    (turn0111 slow w (codeRev ts [o]))

def packedFront (u : Word) : P := enc (front u)

theorem packed_entry (slow : Bool) :
    runP (parent slow) 2 startP = some (packedFront [o,o]) := by
  have h := enc_run slow 2 (⟨0,[],[]⟩ : S)
  rw [blank_entry] at h
  exact h.symm

theorem packed00 (slow : Bool) (ts : List Tok) (w : Word) :
    runP (parent slow) (retClock slow ts 0)
      (packedFront (o::input ts ([z,z]++w))) =
      some (packedFront (o::z::output ts ([o,z,o]++w))) := by
  unfold packedFront
  rw [← enc_run,return00]; rfl

theorem packed0110 (slow : Bool) (ts : List Tok) (w : Word) :
    runP (parent slow) (retClock slow ts 4)
      (packedFront (o::input ts ([z,o,o,z]++w))) =
      some (packedFront (o::z::output ts ([o,z,z,o,o]++w))) := by
  unfold packedFront
  rw [← enc_run,return0110]; rfl

theorem packed0111 (slow : Bool) (ts : List Tok) (w : Word) :
    runP (parent slow) (stopClock slow ts)
      (packedFront (o::input ts ([z,o,o,o]++w))) =
      some (enc (gate w (codeRev ts [o]))) := by
  unfold packedFront
  rw [← enc_run,return0111]; rfl

theorem gate_read (w r : Word) : readP (enc (gate w r)) = (0,true) := by
  rw [enc_read]; rfl

#print axioms packed_entry
#print axioms packed00
#print axioms packed0110
#print axioms packed0111
#print axioms gate_read
end BB6.Agent3OneLBReturn
