import Raw40OrientedCrossing
import PackedZipper
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent19OrientedCrossing
open BB6Coverage Agent50Zipper Agent42Crossing Agent13PackedZipper

/-- Packed naturals are an injective representation of the zero-extended
    tape, even when the concrete list has extra trailing blanks. -/
theorem pack_eq_getD (a b : List Bool) (h : pack a = pack b) (i : Nat) :
    a.getD i false = b.getD i false := by
  induction i generalizing a b with
  | zero =>
    have H := congrArg (fun n : Nat => n%2) h
    rw [pack_head,pack_head] at H
    have he : a.headD false = b.headD false := by
      cases ha : a.headD false <;> cases hb : b.headD false <;> simp_all
    cases a <;> cases b <;> simpa using he
  | succ i ih =>
    have ht : pack a.tail = pack b.tail := by
      rw [← pack_tail,← pack_tail,h]
    have H := ih a.tail b.tail ht
    cases a <;> cases b <;> simpa using H

def packedGoal (c : Certificate) : P := ⟨0,0,pack ((expand 0 c.right).map Cell.bit)⟩

theorem entry_sound_packed (p : PartialMachine) (c : Certificate) (init : Z) (entry : Nat)
    (he : runP p entry (encode init) = some (packedGoal c)) (m : Machine) (hm : compatible p m) :
    ∃ h, run m entry (embed init) = some (family c h 0) := by
  have H := (encode_run p entry init).trans he
  cases hz : zrun p entry init with
  | none => simp [hz] at H
  | some z =>
    have heq : encode z = packedGoal c := by simpa [hz] using H
    have hq : z.q = 0 := congrArg P.q heq
    have hl : pack z.l = pack [] := congrArg P.l heq
    have hr : pack z.r = pack ((expand 0 c.right).map Cell.bit) := congrArg P.r heq
    have hf : embed z = family c z.h 0 :=
      embed_congr _ _ hq rfl (pack_eq_getD _ _ hl) (pack_eq_getD _ _ hr)
    have H := zrun_sound p m hm entry init z hz
    exact ⟨z.h,by rwa [hf] at H⟩

/-- The recurrence does not depend on the absolute entry head coordinate. -/
theorem never_oriented_packed (f s : Bool) (p : PartialMachine) (c : Certificate)
    (entry : Nat)
    (hcert : certOK (orientPartial f s p) c) (hn : c.head.events ≠ [])
    (hb : inputBlank c) (hr : recOK c)
    (he : runP (orientPartial f s p) entry (encode (initialZ s)) = some (packedGoal c))
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have hcompat := orient_compatible f s p m hm
  have arbitrarily : ∀ n, ∃ k j, n≤k ∧
      run (orientMachine f s m) k (embed (initialZ s)) = some (family c j n) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨h,hentry⟩ := entry_sound_packed _ _ _ _ he _ hcompat
      exact ⟨entry,h,by omega,hentry⟩
    | succ n ih =>
      obtain ⟨k,j,hk,h1⟩ := ih
      obtain ⟨cost,j',hp,h2⟩ := recurrence _ _ hcert hn hb hr _ hcompat j n
      exact ⟨k+cost,j',by omega,by rw [run_append,h1]; exact h2⟩
  intro n
  obtain ⟨k,j,hk,h1⟩ := arbitrarily n
  have H := run_orient f s m k (embed (initialZ s))
  rw [initial_orient,h1] at H
  change run m k blank = some (orientConfig f s (family c j n)) at H
  rw [show k=n+(k-n) by omega,run_append] at H
  change (run m n (emptyAt 0)).isSome = true
  cases hh : run m n (emptyAt 0) with
  | none => simp [hh] at H
  | some z => rfl

/-- Boolean reflection avoids building a nested Decidable proof for every
    event and every adjacent interface of a large finite crossing script. -/
def validB (p : PartialMachine) (out mark : Bool) : Bool → Mode → List Ev → Bool
  | b, .active q, [] => (b == out) && mark && (q == 0)
  | b, .idle _, [] => (b == out) && !mark
  | b, .active q, e::es =>
    !e.entering && decide (p (q,b) = some (some ⟨e.write,e.right,e.q⟩)) &&
      validB p out mark e.write (.idle e.right) es
  | b, .idle fromRight, e::es =>
    e.entering && (e.right == !fromRight) && validB p out mark b (.active e.q) es

theorem validB_iff (p : PartialMachine) (out mark b : Bool) (m : Mode) (es : List Ev) :
    validB p out mark b m es = true ↔ valid p out mark b m es := by
  induction es generalizing b m with
  | nil => cases m <;> simp [validB,valid,and_assoc]
  | cons e es ih =>
    cases m <;> simp [validB,valid,ih,and_assoc]

def localB (p : PartialMachine) (c : Cell) (m : Mode) : Bool :=
  validB p c.out c.mark c.bit m c.events

theorem localB_sound (p : PartialMachine) (c : Cell) (m : Mode)
    (h : localB p c m = true) : localOK p c m :=
  (validB_iff _ _ _ _ _ _).mp h

def chainB (p : PartialMachine) (d : Bool) (a : List (Bool × Fin 6)) :
    List Cell → List (Bool × Fin 6) → Bool
  | [], b => a == b
  | c::cs, b => (a == edge c (!d)) && localB p c (.idle (!d)) &&
      chainB p d (edge c d) cs b

theorem chainB_iff (p : PartialMachine) (d : Bool) (a b : List (Bool × Fin 6)) (xs : List Cell) :
    chainB p d a xs b = true ↔ chain p d a xs b := by
  induction xs generalizing a with
  | nil => simp [chainB,chain]
  | cons x xs ih => simp [chainB,chain,localB,localOK,validB_iff,ih,and_assoc]

theorem chainB_sound (p : PartialMachine) (d : Bool) (a b : List (Bool × Fin 6))
    (xs : List Cell) (h : chainB p d a xs b = true) : chain p d a xs b :=
  (chainB_iff p d a b xs).mp h

#print axioms never_oriented_packed
#print axioms chainB_sound
end BB6Coverage.Agent19OrientedCrossing
