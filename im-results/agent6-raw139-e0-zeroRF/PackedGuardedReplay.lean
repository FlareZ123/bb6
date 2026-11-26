import GuardedTail
set_option maxHeartbeats 0
namespace BB6.Agent6PackedReplay
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent6GuardedTail

def packWord : List Bool → Nat
  | [] => 1
  | a::l => 2 * packWord l + a.toNat

theorem packWord_pos (l : List Bool) : 0 < packWord l := by
  induction l with
  | nil => decide
  | cons a l ih => simp only [packWord]; omega

def head (n : Nat) : Bool := if n = 1 then false else n % 2 == 1
def tail (n : Nat) : Nat := if n = 1 then 1 else n / 2
def push (a : Bool) (n : Nat) := 2*n+a.toNat

theorem head_pack (l : List Bool) : head (packWord l) = l.headD false := by
  cases l with
  | nil => rfl
  | cons a l =>
    have h := packWord_pos l
    cases a <;> simp [head,packWord,Bool.toNat] <;> omega

theorem tail_pack (l : List Bool) : tail (packWord l) = packWord l.tail := by
  cases l with
  | nil => rfl
  | cons a l =>
    have h := packWord_pos l
    cases a <;> simp [tail,packWord,Nat.mul_add_div (by decide : 0 < 2),Bool.toNat] <;> omega

theorem packWord_eq_one (l : List Bool) : packWord l = 1 ↔ l = [] := by
  cases l with
  | nil => simp [packWord]
  | cons a l => have h := packWord_pos l; simp [packWord]; omega

theorem packWord_inj : Function.Injective packWord := by
  intro l r h
  induction l generalizing r with
  | nil => exact ((packWord_eq_one r).mp h.symm).symm
  | cons a l ih =>
    cases r with
    | nil => have h' := (packWord_eq_one (a::l)).mp h; contradiction
    | cons b r =>
      have hh := congrArg head h
      rw [head_pack,head_pack] at hh
      have ht := congrArg tail h
      rw [tail_pack,tail_pack] at ht
      have hh' : a = b := hh
      have ht' : l = r := ih ht
      subst b; subst r; rfl

structure PZ where
  q : Fin 6
  l : Nat
  r : Nat
  deriving DecidableEq

def pack (z : Z0) : PZ := ⟨z.q,packWord z.l,packWord z.r⟩

theorem pack_inj : Function.Injective pack := by
  intro a b h
  cases a; cases b
  simp only [pack,PZ.mk.injEq] at h
  rcases h with ⟨hq,hl,hr⟩
  cases hq; cases packWord_inj hl; cases packWord_inj hr; rfl

def pmove (mv : Move) (z : PZ) : PZ :=
  if mv.right then ⟨mv.next,push (head z.r) (push mv.write (tail z.l)),tail z.r⟩
  else ⟨mv.next,tail z.l,push mv.write z.r⟩
def pstep (p : PartialMachine) (guard : Bool) (z : PZ) : Option PZ :=
  if guard && z.l == 1 then none else
    ((p (z.q,head z.l)).bind id).map (fun mv => pmove mv z)
def slowStep (p : PartialMachine) (guard : Bool) (z : Z0) : Option Z0 :=
  if guard then guardedStep p z else step0 p z

theorem pack_move (mv : Move) (z : Z0) : pack (move0 mv z) = pmove mv (pack z) := by
  cases h : mv.right <;> simp [pack,move0,pmove,h,head_pack,tail_pack,push,packWord]

theorem pack_step (p : PartialMachine) (guard : Bool) (z : Z0) :
    pstep p guard (pack z) = (slowStep p guard z).map pack := by
  have hguard : ((pack z).l == 1) = z.l.isEmpty := by
    cases hz : z.l with
    | nil => simp [pack,hz,packWord]
    | cons a l => simp [pack,hz,packWord_eq_one]
  unfold pstep slowStep guardedStep
  rw [hguard]
  have hhead : head (pack z).l = z.l.headD false := head_pack z.l
  cases guard <;> cases he : z.l.isEmpty <;>
    simp only [Bool.false_and,Bool.true_and,Bool.false_eq_true,ite_false,ite_true,Option.map_none,step0,hhead]
  all_goals
    change (((p (z.q,z.l.headD false)).bind id).map (fun mv => pmove mv (pack z))) =
      ((((p (z.q,z.l.headD false)).bind id).map (fun mv => move0 mv z))).map pack
    cases hm : (p (z.q,z.l.headD false)).bind id with
    | none => rfl
    | some mv => exact congrArg some (pack_move mv z).symm

def prun (p : PartialMachine) (guard : Bool) : Nat → PZ → Option PZ :=
  Nat.rec (fun z => some z) (fun _ rec z => (pstep p guard z).bind rec)
theorem prun_join {p : PartialMachine} {guard : Bool} {n k : Nat} {a b c : PZ}
    (h : prun p guard n a = some b) (g : prun p guard k b = some c) :
    prun p guard (n+k) a = some c := by
  induction n generalizing a with
  | zero =>
    have h' : a = b := Option.some.inj h
    subst a; simpa using g
  | succ n ih =>
    change (pstep p guard a).bind (prun p guard n) = some b at h
    rw [Nat.succ_add]
    change (pstep p guard a).bind (prun p guard (n+k)) = some c
    cases hs : pstep p guard a with
    | none => simp [hs] at h
    | some u => exact ih (by simpa [hs] using h)

def srun (p : PartialMachine) (guard : Bool) (n : Nat) (z : Z0) : Option Z0 :=
  if guard then guardedRun p n z else run0 p n z

theorem srun_succ (p : PartialMachine) (guard : Bool) (n : Nat) (z : Z0) :
    srun p guard (n+1) z = (slowStep p guard z).bind (srun p guard n) := by
  cases guard <;> rfl

theorem pack_run (p : PartialMachine) (guard : Bool) (n : Nat) (z : Z0) :
    prun p guard n (pack z) = (srun p guard n z).map pack := by
  induction n generalizing z with
  | zero => cases guard <;> rfl
  | succ n ih =>
    change (pstep p guard (pack z)).bind (prun p guard n) = _
    rw [pack_step,srun_succ]
    cases hs : slowStep p guard z with
    | none => rfl
    | some u => exact ih u

theorem replay_sound (p : PartialMachine) (guard : Bool) (n : Nat) (a b : Z0)
    (h : prun p guard n (pack a) = some (pack b)) : srun p guard n a = some b := by
  apply Option.map_injective pack_inj
  exact (pack_run p guard n a).symm.trans h

#print axioms replay_sound
end BB6.Agent6PackedReplay
