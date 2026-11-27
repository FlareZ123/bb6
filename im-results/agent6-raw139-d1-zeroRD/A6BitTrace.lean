import ZipThreeHoleAudit
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6Coverage.A6BitTrace
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper BB6Coverage.Agent10ZipAudit
open BB6.Agent13BlankDelay BB6.Agent50TNFPilot

def bit (b : Bool) : Nat := if b then 1 else 0
def enc : List Bool → Nat
  | [] => 0
  | b::l => bit b+2*enc l
def hd (n : Nat) : Bool := n%2 == 1
def tl (n : Nat) : Nat := n/2

theorem hd_enc (l : List Bool) : hd (enc l) = l.headD false := by
  cases l with
  | nil => rfl
  | cons b l => cases b <;> simp [hd,enc,bit,Nat.add_mul_mod_self_left]
theorem tl_enc (l : List Bool) : tl (enc l) = enc l.tail := by
  cases l with
  | nil => rfl
  | cons b l => cases b <;> simp [tl,enc,bit] <;> omega

structure P where
  q : Fin 6
  l : Nat
  r : Nat
  deriving DecidableEq, Repr

def encZ (z : Z0) : P := ⟨z.q,enc z.l,enc z.r⟩
def stepP (p : PartialMachine) (z : P) : Option P :=
  ((p (z.q,hd z.l)).bind id).map fun mv =>
    if mv.right then ⟨mv.next,bit (hd z.r)+2*(bit mv.write+2*tl z.l),tl z.r⟩
    else ⟨mv.next,tl z.l,bit mv.write+2*z.r⟩
theorem step_enc (p : PartialMachine) (z : Z0) : stepP p (encZ z) = (step0 p z).map encZ := by
  simp only [stepP,encZ,hd_enc,tl_enc,step0]
  cases h : (p (z.q,z.l.headD false)).bind id with
  | none => rfl
  | some mv => cases hr : mv.right <;> simp [move0,hr,encZ,enc,hd_enc,tl_enc]

def runP (p : PartialMachine) : Nat → P → Option P
  | 0,z => some z
  | n+1,z => (stepP p z).bind (runP p n)
theorem run_enc (p : PartialMachine) (n : Nat) (z : Z0) : runP p n (encZ z) = (run0 p n z).map encZ := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [runP,step_enc,run0]
    cases hs : step0 p z with
    | none => rfl
    | some t => exact ih t

def Reach (p : PartialMachine) (n : Nat) (b : P) : Prop :=
  ∃ z, run0 p n ⟨0,[],[]⟩ = some z ∧ encZ z = b

theorem reach0 (p : PartialMachine) : Reach p 0 ⟨0,0,0⟩ := ⟨_,rfl,rfl⟩
theorem reach_extend {p : PartialMachine} {n k : Nat} {a b : P}
    (h : Reach p n a) (hh : runP p k a = some b) : Reach p (n+k) b := by
  obtain ⟨z,hz,rfl⟩ := h
  rw [run_enc] at hh
  cases he : run0 p k z with
  | none => simp [he] at hh
  | some u => exact ⟨u,join0 hz he,by simpa [he] using hh⟩
theorem reach_read (p : PartialMachine) (n : Nat) (b : P) (h : Reach p n b) :
    (knownRun p n).map readSlot = some (b.q,hd b.l) := by
  obtain ⟨z,hz,hb⟩ := h
  have H : (zrun p n start).map project = some z := (run_project p n start).trans hz
  rw [knownRun_zip]
  cases hq : zrun p n start with
  | none => simp [hq] at H
  | some u =>
    have hu : project u = z := Option.some.inj (by simpa only [hq,Option.map_some] using H)
    rw [← hb,← hu]
    simp [read_embed,project,encZ,hd_enc]
#print axioms reach_extend
#print axioms reach_read
end BB6Coverage.A6BitTrace
