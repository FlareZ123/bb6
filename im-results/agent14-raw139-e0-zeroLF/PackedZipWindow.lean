import E0LFZipSideCycle
set_option maxHeartbeats 0
namespace BB6Coverage.Agent14PackedWindow
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent3ZipSideCycle

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
  h : Int
  l : Nat
  r : Nat
  deriving DecidableEq

def pack (z : Z) : PZ := ⟨z.q,z.h,packWord z.l,packWord z.r⟩

theorem pack_inj : Function.Injective pack := by
  intro a b h
  cases a; cases b
  simp only [pack,PZ.mk.injEq] at h
  rcases h with ⟨hq,hh,hl,hr⟩
  cases hq; cases hh; cases packWord_inj hl; cases packWord_inj hr; rfl

def pmove (mv : Move) (z : PZ) : PZ :=
  if mv.right then ⟨mv.next,z.h+1,push (head z.r) (push mv.write (tail z.l)),tail z.r⟩
  else ⟨mv.next,z.h-1,tail z.l,push mv.write z.r⟩
def permitted (bound : Option Int) (h : Int) : Bool :=
  match bound with
  | none => true
  | some b => decide (h ≤ b)
def pstep (p : PartialMachine) (bound : Option Int) (z : PZ) : Option PZ :=
  if permitted bound z.h then ((p (z.q,head z.l)).bind id).map (fun mv => pmove mv z) else none

def slowStep (p : PartialMachine) (bound : Option Int) (z : Z) : Option Z :=
  if permitted bound z.h then step p z else none

theorem pack_move (mv : Move) (z : Z) : pack (move mv z) = pmove mv (pack z) := by
  cases h : mv.right <;> simp [pack,move,pmove,h,head_pack,tail_pack,push,packWord]

theorem pack_step (p : PartialMachine) (bound : Option Int) (z : Z) :
    pstep p bound (pack z) = (slowStep p bound z).map pack := by
  unfold pstep slowStep
  change (if permitted bound z.h then ((p (z.q,head (packWord z.l))).bind id).map (fun mv => pmove mv (pack z)) else none) = _
  rw [head_pack]
  split
  · unfold step
    cases hm : (p (z.q,z.l.headD false)).bind id with
    | none => rfl
    | some mv => exact congrArg some (pack_move mv z).symm
  · rfl

def prun (p : PartialMachine) (bound : Option Int) : Nat → PZ → Option PZ
  | 0,z => some z
  | n+1,z => (pstep p bound z).bind (prun p bound n)

theorem prun_join {p : PartialMachine} {bound : Option Int} {n k : Nat} {a b c : PZ}
    (h : prun p bound n a = some b) (g : prun p bound k b = some c) :
    prun p bound (n+k) a = some c := by
  induction n generalizing a with
  | zero =>
    have h' : a = b := Option.some.inj h
    subst a; simpa using g
  | succ n ih =>
    change (pstep p bound a).bind (prun p bound n) = some b at h
    rw [Nat.succ_add]
    change (pstep p bound a).bind (prun p bound (n+k)) = some c
    cases hs : pstep p bound a with
    | none => simp [hs] at h
    | some u => exact ih (by simpa [hs] using h)

def srun (p : PartialMachine) (bound : Option Int) (n : Nat) (z : Z) : Option Z :=
  match bound with
  | none => zrun p n z
  | some b => zwindow p b n z

theorem srun_succ (p : PartialMachine) (bound : Option Int) (n : Nat) (z : Z) :
    srun p bound (n+1) z = (slowStep p bound z).bind (srun p bound n) := by
  cases bound with
  | none => rfl
  | some b => simp only [srun,zwindow,slowStep,permitted,decide_eq_true_eq]; split <;> rfl

theorem pack_run (p : PartialMachine) (bound : Option Int) (n : Nat) (z : Z) :
    prun p bound n (pack z) = (srun p bound n z).map pack := by
  induction n generalizing z with
  | zero => cases bound <;> rfl
  | succ n ih =>
    change (pstep p bound (pack z)).bind (prun p bound n) = _
    rw [pack_step,srun_succ]
    cases hs : slowStep p bound z with
    | none => rfl
    | some u => exact ih u

theorem replay_sound (p : PartialMachine) (bound : Option Int) (n : Nat) (a b : Z)
    (h : prun p bound n (pack a) = some (pack b)) : srun p bound n a = some b := by
  apply Option.map_injective pack_inj
  exact (pack_run p bound n a).symm.trans h

#print axioms replay_sound
end BB6Coverage.Agent14PackedWindow
