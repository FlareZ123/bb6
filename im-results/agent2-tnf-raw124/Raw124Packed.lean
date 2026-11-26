import SweepPumping
import ZipThreeHoleAudit
namespace BB6.Agent4.Raw124Packed
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent10ZipAudit BB6Coverage.Agent10ZipAudit
open BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot

structure PZ where
  q : Fin 6
  l : Nat
  r : Nat
  deriving DecidableEq, Repr

def pack : List Bool → Nat
  | [] => 0
  | b::bs => b.toNat + 2 * pack bs

def enc (z : Z0) : PZ := ⟨z.q,pack z.l,pack z.r⟩

theorem pack_head (xs : List Bool) : (pack xs % 2 == 1) = xs.headD false := by
  cases xs with
  | nil => rfl
  | cons b bs => cases b <;> simp [pack,Bool.toNat] <;> omega

theorem pack_tail (xs : List Bool) : pack xs / 2 = pack xs.tail := by
  cases xs with
  | nil => rfl
  | cons b bs => cases b <;> simp [pack,Bool.toNat] <;> omega

theorem pack_head_nat (xs : List Bool) : pack xs % 2 = (xs.headD false).toNat := by
  cases xs with
  | nil => rfl
  | cons b bs => cases b <;> simp [pack,Bool.toNat] <;> omega

def pmove (mv : Move) (z : PZ) : PZ :=
  if mv.right then ⟨mv.next,z.r % 2 + 2*(mv.write.toNat + 2*(z.l/2)),z.r/2⟩
  else ⟨mv.next,z.l/2,mv.write.toNat+2*z.r⟩

def pstep (p : PartialMachine) (z : PZ) : Option PZ :=
  ((p (z.q,z.l % 2 == 1)).bind id).map (fun mv => pmove mv z)

theorem enc_move (mv : Move) (z : Z0) : enc (move0 mv z) = pmove mv (enc z) := by
  cases h : mv.right <;> simp [enc,move0,pmove,h,pack,pack_tail,pack_head_nat]

theorem enc_step (p : PartialMachine) (z : Z0) : (step0 p z).map enc = pstep p (enc z) := by
  unfold step0 pstep
  simp only [enc,pack_head,Option.map_map]
  cases h : (p (z.q,z.l.headD false)).bind id with
  | none => rfl
  | some mv => exact congrArg some (enc_move mv z)

def prun (p : PartialMachine) : Nat → PZ → Option PZ
  | 0,z => some z
  | n+1,z => (pstep p z).bind (prun p n)

theorem prun_add (p : PartialMachine) (n k : Nat) (z : PZ) :
    prun p (n+k) z = (prun p n z).bind (prun p k) := by
  induction n generalizing z with
  | zero => simp [prun]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    simp only [prun]
    cases h : pstep p z with
    | none => rfl
    | some t => exact ih t

theorem pjoin {p : PartialMachine} {n k : Nat} {a b c : PZ}
    (h : prun p n a = some b) (g : prun p k b = some c) : prun p (n+k) a = some c := by
  rw [prun_add,h]; exact g

theorem pjoin_fixed (p : PartialMachine) (n k N : Nat) (a b c : PZ)
    (h : prun p n a = some b) (g : prun p k b = some c) (hn : n+k=N) : prun p N a = some c := by
  subst N; exact pjoin h g

theorem enc_run (p : PartialMachine) (n : Nat) (z : Z0) :
    (run0 p n z).map enc = prun p n (enc z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [run0,prun,← enc_step]
    cases h : step0 p z with
    | none => rfl
    | some t => exact ih t

theorem packed_read {p : PartialMachine} {n : Nat} {z : PZ}
    (h : prun p n ⟨0,0,0⟩ = some z) : zipRead p n = some (z.q,z.l % 2 == 1) := by
  have H := (enc_run p n ⟨0,[],[]⟩).trans h
  have J := run_project p n BB6Coverage.Agent31Pump.start
  change (BB6Coverage.Agent50Zipper.zrun p n BB6Coverage.Agent31Pump.start).map project = run0 p n ⟨0,[],[]⟩ at J
  rw [← J,Option.map_map] at H
  unfold zipRead
  cases hs : BB6Coverage.Agent50Zipper.zrun p n BB6Coverage.Agent31Pump.start with
  | none => simp [hs] at H
  | some t =>
    have hz : enc (project t) = z := Option.some.inj (by simpa [hs] using H)
    subst z
    simp [enc,project,pack_head]

theorem packed_last {p : PartialMachine} {n B : Nat} {z : PZ}
    (h : prun p n ⟨0,0,0⟩ = some z)
    (hno : p (z.q,z.l % 2 == 1) = none)
    (hw : weightOK p (z.q,z.l % 2 == 1) n B = true)
    (hr : restOK p (z.q,z.l % 2 == 1) = true) :
    zipCheck B p (.last n (z.q,z.l % 2 == 1)) = true := by
  rw [zipCheck.eq_1]
  simp [zipQueryOK,packed_read h,hno,hw,hr]

end BB6.Agent4.Raw124Packed
