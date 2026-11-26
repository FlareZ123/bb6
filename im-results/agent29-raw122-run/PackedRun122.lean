import Raw122Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedRun
open BB6Coverage BB6Coverage.Agent31Pump
open BB6Coverage.Agent50Zipper
open BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

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

theorem pack_head_eq (xs : List Bool) : (pack xs % 2 == 1) = xs.headD false := by
  rw [pack_head]
  cases xs.headD false <;> rfl

structure PZ where
  q : Fin 6
  l : Nat
  r : Nat
  deriving DecidableEq, Repr

def enc (z : Z0) : PZ := ⟨z.q, pack z.l, pack z.r⟩
def pmove (mv : Move) (z : PZ) : PZ :=
  if mv.right then ⟨mv.next, z.r % 2 + 2 * (mv.write.toNat + 2 * (z.l / 2)), z.r / 2⟩
  else ⟨mv.next, z.l / 2, mv.write.toNat + 2 * z.r⟩

def pstep (p : PartialMachine) (z : PZ) : Option PZ :=
  (p (z.q,z.l % 2 == 1)).bind id |>.map (fun mv => pmove mv z)

theorem enc_move (mv : Move) (z : Z0) : enc (move0 mv z) = pmove mv (enc z) := by
  cases h : mv.right <;> simp [enc,move0,pmove,h,pack,pack_head,pack_tail]

theorem enc_step (p : PartialMachine) (z : Z0) : (step0 p z).map enc = pstep p (enc z) := by
  unfold step0 pstep
  change (Option.map (fun mv => move0 mv z) ((p (z.q,z.l.headD false)).bind id)).map enc =
    (((p (z.q,pack z.l % 2 == 1)).bind id)).map (fun mv => pmove mv (enc z))
  rw [pack_head_eq]
  cases h : p (z.q,z.l.headD false) with
  | none => rfl
  | some op => cases op with
    | none => rfl
    | some mv => simp [enc_move]

def prun (p : PartialMachine) : Nat → PZ → Option PZ
  | 0,z => some z
  | n+1,z => (pstep p z).bind (prun p n)

theorem prun_add (p : PartialMachine) (n k : Nat) (z : PZ) :
    prun p (n+k) z = (prun p n z).bind (prun p k) := by
  induction n generalizing z with
  | zero => simp [prun]
  | succ n ih =>
    rw [show n+1+k = n+k+1 by omega,prun,prun]
    cases h : pstep p z <;> simp [h,ih]

theorem pjoin {p : PartialMachine} {n k : Nat} {a b c : PZ}
    (h : prun p n a = some b) (g : prun p k b = some c) : prun p (n+k) a = some c := by
  rw [prun_add,h]; exact g

theorem enc_run (p : PartialMachine) (n : Nat) (z : Z0) :
    (run0 p n z).map enc = prun p n (enc z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [run0,prun,← enc_step]
    cases h : step0 p z <;> simp [h,ih]

theorem packed_read {p : PartialMachine} {n : Nat} {z : PZ}
    (h : prun p n ⟨0,0,0⟩ = some z) :
    BB6Coverage.Agent10ZipAudit.zipRead p n = some (z.q,z.l % 2 == 1) := by
  have H := (enc_run p n ⟨0,[],[]⟩).trans h
  have J := run_project p n start
  change (zrun p n start).map project = run0 p n ⟨0,[],[]⟩ at J
  rw [← J,Option.map_map] at H
  unfold BB6Coverage.Agent10ZipAudit.zipRead
  cases hs : zrun p n start with
  | none => simp [hs] at H
  | some t =>
    have hz : enc (project t) = z := Option.some.inj (by simpa [hs] using H)
    subst z
    simp [enc, project, pack_head_eq]

theorem packed_last {p : PartialMachine} {n B : Nat} {z : PZ}
    (h : prun p n ⟨0,0,0⟩ = some z)
    (hno : p (z.q,z.l % 2 == 1) = none)
    (hw : weightOK p (z.q,z.l % 2 == 1) n B = true)
    (hr : restOK p (z.q,z.l % 2 == 1) = true) :
    zipCheck B p (.last n (z.q,z.l % 2 == 1)) = true := by
  rw [zipCheck.eq_1]
  simp [zipQueryOK, packed_read h, hno, hw, hr]

#print axioms packed_last
end BB6Coverage.Agent29PackedRun
