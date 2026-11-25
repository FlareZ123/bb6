import ZipAuditCore
namespace BB6Coverage.Agent13PackedZipper
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6Coverage.Agent10ZipAudit

def pack : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * pack bs

theorem pack_head (xs : List Bool) : pack xs % 2 = (xs.headD false).toNat := by
  cases xs with
  | nil => rfl
  | cons b bs => cases b <;> simp [pack, Bool.toNat] <;> omega

theorem pack_tail (xs : List Bool) : pack xs / 2 = pack xs.tail := by
  cases xs with
  | nil => rfl
  | cons b bs => cases b <;> simp [pack, Bool.toNat] <;> omega

structure P where
  q : Fin 6
  l : Nat
  r : Nat
  deriving DecidableEq, Repr

def encode (z : Z) : P := ⟨z.q, pack z.l, pack z.r⟩
def readP (z : P) : Slot := (z.q, z.l % 2 == 1)

theorem encode_read (z : Z) : readP (encode z) = (z.q, z.l.headD false) := by
  unfold readP encode
  rw [pack_head]
  cases z.l.headD false <;> rfl

def moveP (mv : Move) (z : P) : P :=
  if mv.right then
    ⟨mv.next, z.r % 2 + 2 * (mv.write.toNat + 2 * (z.l / 2)), z.r / 2⟩
  else
    ⟨mv.next, z.l / 2, mv.write.toNat + 2 * z.r⟩

theorem encode_move (mv : Move) (z : Z) : encode (move mv z) = moveP mv (encode z) := by
  cases h : mv.right <;> simp [encode, move, moveP, h, pack, pack_head, pack_tail]

def stepP (p : PartialMachine) (z : P) : Option P :=
  ((p (readP z)).bind id).map (fun mv => moveP mv z)

theorem encode_step (p : PartialMachine) (z : Z) :
    (step p z).map encode = stepP p (encode z) := by
  unfold step stepP
  rw [encode_read]
  cases h : (p (z.q,z.l.headD false)).bind id with
  | none => rfl
  | some mv => simp [encode_move]

def runP (p : PartialMachine) : Nat → P → Option P
  | 0,z => some z
  | n+1,z => (stepP p z).bind (runP p n)

theorem encode_run (p : PartialMachine) (n : Nat) (z : Z) :
    (zrun p n z).map encode = runP p n (encode z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [zrun,runP,← encode_step]
    cases h : step p z with
    | none => rfl
    | some t => exact ih t

theorem runP_add (p : PartialMachine) (n k : Nat) (z : P) :
    runP p (n+k) z = (runP p n z).bind (runP p k) := by
  induction n generalizing z with
  | zero => simp [runP]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    simp only [runP]
    cases stepP p z with
    | none => rfl
    | some t => exact ih t

theorem joinP {p : PartialMachine} {n k : Nat} {a b c : P}
    (h : runP p n a = some b) (g : runP p k b = some c) :
    runP p (n+k) a = some c := by
  rw [runP_add,h]; exact g

def startP : P := ⟨0,0,0⟩

def readRunP (p : PartialMachine) (n : Nat) : Option Slot :=
  (runP p n startP).map readP

theorem readRunP_eq (p : PartialMachine) (n : Nat) : readRunP p n = zipRead p n := by
  unfold readRunP zipRead
  rw [show startP = encode start from rfl, ← encode_run]
  cases h : zrun p n start with
  | none => rfl
  | some z => simp [encode_read]

#print axioms readRunP_eq
end BB6Coverage.Agent13PackedZipper
