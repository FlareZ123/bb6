import SweepPumping
namespace BB6.Agent11PackedPump
open BB6Coverage BB6Coverage.Agent31Pump

/-- A finite tape word is represented least-significant-bit first, with a high sentinel 1. -/
def packWord : List Bool → Nat
  | [] => 1
  | b::bs => 2 * packWord bs + b.toNat

theorem pack_pos (xs : List Bool) : 0 < packWord xs := by
  induction xs with
  | nil => decide
  | cons b bs ih => simp only [packWord]; omega

theorem pack_nil (xs : List Bool) : packWord xs = 1 ↔ xs = [] := by
  cases xs with
  | nil => simp [packWord]
  | cons b bs => have h := pack_pos bs; simp only [packWord,List.cons_ne_nil,iff_false]; omega

def push (b : Bool) (x : Nat) : Nat := 2*x+b.toNat
def pop (x : Nat) : Nat := if x = 1 then 1 else x/2
def top (x : Nat) : Bool := x ≠ 1 && x%2 == 1

theorem push_pack (b : Bool) (xs : List Bool) : push b (packWord xs) = packWord (b::xs) := rfl
theorem pop_pack (xs : List Bool) : pop (packWord xs) = packWord xs.tail := by
  cases xs with
  | nil => rfl
  | cons b bs =>
    have h := pack_pos bs
    cases b with
    | false =>
      change (if 2*packWord bs+0 = 1 then 1 else (2*packWord bs+0)/2) = packWord bs
      split <;> omega
    | true =>
      change (if 2*packWord bs+1 = 1 then 1 else (2*packWord bs+1)/2) = packWord bs
      split <;> omega

theorem top_pack (xs : List Bool) : top (packWord xs) = xs.headD false := by
  cases xs with
  | nil => rfl
  | cons b bs =>
    have h := pack_pos bs
    cases b <;> simp [top,packWord,Bool.toNat] <;> omega

theorem pack_inj {xs ys : List Bool} (h : packWord xs = packWord ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => exact ((pack_nil ys).mp h.symm).symm
  | cons x xs ih =>
    cases ys with
    | nil => exact (pack_nil (x::xs)).mp h
    | cons y ys =>
      have ht := congrArg top h
      have hh : x = y := by simpa only [top_pack,List.headD_cons] using ht
      have hp := congrArg pop h
      have htl : packWord xs = packWord ys := by simpa only [pop_pack,List.tail_cons] using hp
      subst y
      rw [ih htl]

structure PZ where
  q : Fin 6
  l : Nat
  r : Nat
  deriving DecidableEq, Repr

def pack (z : Z0) : PZ := ⟨z.q,packWord z.l,packWord z.r⟩

theorem pack_injective {a b : Z0} (h : pack a = pack b) : a = b := by
  cases a; cases b
  simp only [pack,PZ.mk.injEq] at h
  obtain ⟨hq,hl,hr⟩ := h
  congr <;> first | exact hq | exact pack_inj hl | exact pack_inj hr

def move (mv : Move) (z : PZ) : PZ :=
  if mv.right then ⟨mv.next,push (top z.r) (push mv.write (pop z.l)),pop z.r⟩
  else ⟨mv.next,pop z.l,push mv.write z.r⟩

theorem move_pack (mv : Move) (z : Z0) : move mv (pack z) = pack (move0 mv z) := by
  cases h : mv.right <;> simp only [move,move0,h,Bool.false_eq_true,ite_false,ite_true,pack,top_pack,pop_pack,push_pack]

def step (p : PartialMachine) (z : PZ) : Option PZ :=
  ((p (z.q,top z.l)).bind id).map (fun mv => move mv z)

theorem step_pack (p : PartialMachine) (z : Z0) : step p (pack z) = (step0 p z).map pack := by
  simp only [step,pack,top_pack,step0]
  change ((p (z.q,z.l.headD false)).bind id).map (fun mv => move mv (pack z)) = _
  cases h : (p (z.q,z.l.headD false)).bind id with
  | none => rfl
  | some mv => simp only [Option.map_some,move_pack]

def run (p : PartialMachine) : Nat → PZ → Option PZ
  | 0,z => some z
  | n+1,z => (step p z).bind (run p n)

theorem run_pack (p : PartialMachine) (n : Nat) (z : Z0) : run p n (pack z) = (run0 p n z).map pack := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [run,run0,step_pack]
    cases step0 p z with
    | none => rfl
    | some t => exact ih t

theorem run_sound {p : PartialMachine} {n : Nat} {a b : Z0} (h : run p n (pack a) = some (pack b)) :
    run0 p n a = some b := by
  rw [run_pack] at h
  cases hr : run0 p n a with
  | none => rw [hr] at h; contradiction
  | some c =>
    have he : pack c = pack b := by rw [hr] at h; exact Option.some.inj h
    rw [pack_injective he]

theorem run_add (p : PartialMachine) (n k : Nat) (z : PZ) :
    run p (n+k) z = (run p n z).bind (run p k) := by
  induction n generalizing z with
  | zero => simp [run]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    simp only [run]
    cases step p z with
    | none => rfl
    | some t => exact ih t

theorem join {p : PartialMachine} {n k : Nat} {a b c : PZ} (h : run p n a = some b) (g : run p k b = some c) : run p (n+k) a = some c := by
  rw [run_add,h]; exact g

/-- The right end is never queried, so an arbitrary right suffix can be appended. -/
def guardRun (p : PartialMachine) : Nat → Z0 → Option Z0
  | 0,z => some z
  | n+1,z => if z.r = [] then none else (step0 p z).bind (guardRun p n)

def appendR (z : Z0) (R : List Bool) : Z0 := { z with r := z.r ++ R }

theorem stepR (p : PartialMachine) (z : Z0) (R : List Bool) (h : z.r ≠ []) :
    step0 p (appendR z R) = (step0 p z).map (fun t => appendR t R) := by
  cases z with
  | mk q l r =>
    cases r with
    | nil => exact False.elim (h rfl)
    | cons b r =>
      change ((p (q,l.headD false)).bind id).map _ = (((p (q,l.headD false)).bind id).map _).map _
      cases hv : (p (q,l.headD false)).bind id with
      | none => rfl
      | some mv => cases hd : mv.right <;> simp [appendR,move0,hd]

theorem guard_tail (p : PartialMachine) (n : Nat) (a b : Z0) (R : List Bool) (h : guardRun p n a = some b) :
    run0 p n (appendR a R) = some (appendR b R) := by
  induction n generalizing a with
  | zero => have he : a = b := Option.some.inj h; subst b; rfl
  | succ n ih =>
    by_cases he : a.r = []
    · simp [guardRun,he] at h
    · cases hs : step0 p a with
      | none => simp [guardRun,he,hs] at h
      | some t =>
        have ht : guardRun p n t = some b := by simpa [guardRun,he,hs] using h
        rw [run0,stepR p a R he,hs]
        exact ih t ht

def packedGuard (p : PartialMachine) : Nat → PZ → Option PZ
  | 0,z => some z
  | n+1,z => if z.r = 1 then none else (step p z).bind (packedGuard p n)

theorem guard_pack (p : PartialMachine) (n : Nat) (z : Z0) :
    packedGuard p n (pack z) = (guardRun p n z).map pack := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [packedGuard,guardRun,pack,pack_nil]
    by_cases he : z.r = []
    · simp [he]
    · simp only [he,ite_false]
      change ((step p (pack z)).bind (packedGuard p n)) = _
      rw [step_pack]
      cases step0 p z with
      | none => rfl
      | some t => exact ih t

theorem guard_sound {p : PartialMachine} {n : Nat} {a b : Z0} (h : packedGuard p n (pack a) = some (pack b)) :
    guardRun p n a = some b := by
  rw [guard_pack] at h
  cases hr : guardRun p n a with
  | none => rw [hr] at h; contradiction
  | some c =>
    have he : pack c = pack b := by rw [hr] at h; exact Option.some.inj h
    rw [pack_injective he]

theorem packedGuard_add (p : PartialMachine) (n k : Nat) (z : PZ) :
    packedGuard p (n+k) z = (packedGuard p n z).bind (packedGuard p k) := by
  induction n generalizing z with
  | zero => simp [packedGuard]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    by_cases h : z.r = 1
    · simp [packedGuard,h]
    · simp only [packedGuard,h,ite_false]
      cases step p z with
      | none => rfl
      | some t => exact ih t

theorem guardJoin {p : PartialMachine} {n k : Nat} {a b c : PZ} (h : packedGuard p n a = some b) (g : packedGuard p k b = some c) : packedGuard p (n+k) a = some c := by
  rw [packedGuard_add,h]; exact g

#print axioms run_sound
#print axioms guard_sound
#print axioms guard_tail
end BB6.Agent11PackedPump
