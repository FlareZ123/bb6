import OneLCLateCore
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent4E0OneLCLate
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent10ZipAudit BB6Coverage.Agent50Zipper BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot

def value : List Bool → Nat | [] => 0 | b::t => b.toNat+2*value t
def head (n:Nat) : Bool := n%2==1
def push (b:Bool) (n:Nat) : Nat := b.toNat+2*n
theorem value_head (l : List Bool) : head (value l) = l.headD false := by
  cases l with
  | nil => rfl
  | cons b t => cases b <;> simp [head,value,Bool.toNat]
theorem value_tail (l : List Bool) : value l / 2 = value l.tail := by
  cases l with
  | nil => rfl
  | cons b t => cases b <;> simp [value,Bool.toNat] <;> omega
structure N0 where
  q : Fin 6
  l : Nat
  r : Nat
  deriving DecidableEq
def encode (z:Z0) : N0 := ⟨z.q,value z.l,value z.r⟩
def moveN (mv:Move) (z:N0) : N0 :=
  if mv.right then ⟨mv.next,push (head z.r) (push mv.write (z.l/2)),z.r/2⟩
  else ⟨mv.next,z.l/2,push mv.write z.r⟩
def stepN (p:PartialMachine) (z:N0) : Option N0 := ((p (z.q,head z.l)).bind id).map (fun mv=>moveN mv z)
def runN (p:PartialMachine) : Nat → N0 → Option N0 := Nat.rec (fun z=>some z) (fun _ rec z=>(stepN p z).bind rec)
theorem move_encode (mv:Move) (z:Z0) : encode (move0 mv z) = moveN mv (encode z) := by
  cases hd : mv.right <;> simp [move0,moveN,hd,encode,push,value,value_head,value_tail]
theorem step_encode (p:PartialMachine) (z:Z0) : stepN p (encode z) = (step0 p z).map encode := by
  unfold stepN step0
  have hhead : head (encode z).l = z.l.headD false := value_head z.l
  rw [hhead]
  change (((p (z.q,z.l.headD false)).bind id).map (fun mv => moveN mv (encode z))) =
    (((p (z.q,z.l.headD false)).bind id).map (fun mv => move0 mv z)).map encode
  cases hm : (p (z.q,z.l.headD false)).bind id with
  | none => rfl
  | some mv => exact congrArg some (move_encode mv z).symm
theorem run_encode (p:PartialMachine) (n:Nat) (z:Z0) : runN p n (encode z) = (run0 p n z).map encode := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    change (stepN p (encode z)).bind (runN p n) = _
    rw [step_encode,run0]
    cases hs : step0 p z with
    | none => rfl
    | some t => exact ih t
theorem runN_join {p:PartialMachine} {n k:Nat} {a b c:N0} (h:runN p n a=some b) (g:runN p k b=some c) : runN p (n+k) a=some c := by
  induction n generalizing a with
  | zero => have h' : a=b := Option.some.inj h; subst a; simpa using g
  | succ n ih =>
    change (stepN p a).bind (runN p n) = some b at h
    rw [Nat.succ_add]
    change (stepN p a).bind (runN p (n+k)) = some c
    cases hs:stepN p a with
    | none => simp [hs] at h
    | some t => exact ih (by simpa [hs] using h)
theorem read_of_runN {p:PartialMachine} {n:Nat} {v:N0} (h:runN p n ⟨0,0,0⟩ = some v) :
    (knownRun p n).map readSlot = some (v.q,head v.l) := by
  have hh := (run_encode p n ⟨0,[],[]⟩).symm.trans h
  cases hz : run0 p n ⟨0,[],[]⟩ with
  | none => simp [hz] at hh
  | some z =>
    have he : encode z = v := by simpa [hz] using hh
    subst v
    rw [read_of_run0 hz]
    simp [encode,value_head]
#print axioms read_of_runN
#print axioms runN_join
end BB6.Agent4E0OneLCLate
