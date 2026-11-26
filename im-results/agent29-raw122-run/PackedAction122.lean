import PackedSweep122
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedRun
open BB6Coverage BB6Coverage.Agent31Pump

theorem rep_len (xs : List Bool) (n : Nat) : (rep xs n).length = xs.length*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rep,ih,Nat.mul_succ,Nat.add_comm]

theorem pack_rep_mul (xs : List Bool) (n : Nat) :
    pack (rep xs n) * (2^xs.length-1) = pack xs * (2^(xs.length*n)-1) := by
  have hp : 0 < 2^xs.length := Nat.pow_pos (by decide)
  induction n with
  | zero => simp [rep,pack]
  | succ n ih =>
    rw [rep,pack_append,Nat.mul_succ,Nat.pow_add]
    have hp2 : 0 < 2^(xs.length*n) := Nat.pow_pos (by decide)
    have h : (2^(xs.length*n)-1)*2^xs.length + (2^xs.length-1) = 2^(xs.length*n)*2^xs.length-1 := by
      have hle := Nat.mul_le_mul_right (2^xs.length) (show 1 ≤ 2^(xs.length*n) by omega)
      rw [Nat.sub_mul]; simp only [Nat.one_mul] at *; omega
    rw [← h,Nat.mul_add,Nat.add_mul,Nat.mul_assoc,ih]
    ac_rfl

theorem pack_rep (xs : List Bool) (n : Nat) (hn : xs.length > 0) :
    pack (rep xs n) = pack xs * (2^(xs.length*n)-1) / (2^xs.length-1) := by
  rw [← pack_rep_mul]
  exact (Nat.mul_div_cancel _ (by have : 2^1 ≤ 2^xs.length := Nat.pow_le_pow_right (by decide) hn; omega)).symm

#print axioms pack_rep
end BB6Coverage.Agent29PackedRun

namespace BB6Coverage.Agent29PackedRun
open BB6Coverage BB6Coverage.Agent31Pump
structure Motif where
  q : Fin 6
  k : Nat
  right : Bool
  lp : List Bool
  rp : List Bool
  I : List Bool
  O : List Bool

def Motif.Valid (p : PartialMachine) (a : Motif) : Prop :=
  0 < a.I.length ∧ 0 < a.O.length ∧
  if a.right then ∀ L R : List Bool, run0 p a.k ⟨a.q,a.lp++L,a.rp++a.I++R⟩ = some ⟨a.q,a.lp++a.O++L,a.rp++R⟩
  else ∀ L R : List Bool, run0 p a.k ⟨a.q,a.lp++a.I++L,a.rp++R⟩ = some ⟨a.q,a.lp++L,a.rp++a.O++R⟩

def repPacked (xs : List Bool) (n : Nat) : Nat := pack xs * (2^(xs.length*n)-1) / (2^xs.length-1)
def prefRep (xs ys : List Bool) (n : Nat) : Nat := pack xs + 2^xs.length * repPacked ys n

theorem prefRep_eq (xs ys : List Bool) (n : Nat) (h : 0 < ys.length) : prefRep xs ys n = pack (xs++rep ys n) := by
  rw [prefRep,repPacked,← pack_rep ys n h,pack_append]

def applyMotif (a : Motif) (n : Nat) (z : PZ) : Option PZ :=
  let dl := 2^(a.lp.length + if a.right then 0 else a.I.length*n)
  let dr := 2^(a.rp.length + if a.right then a.I.length*n else 0)
  let il := if a.right then pack a.lp else prefRep a.lp a.I n
  let ir := if a.right then prefRep a.rp a.I n else pack a.rp
  if z.q == a.q && z.l % dl == il && z.r % dr == ir then
    let L := z.l / dl
    let R := z.r / dr
    if a.right then some ⟨a.q,prefRep a.lp a.O n + 2^(a.lp.length+a.O.length*n)*L,pack a.rp+2^a.rp.length*R⟩
    else some ⟨a.q,pack a.lp+2^a.lp.length*L,prefRep a.rp a.O n + 2^(a.rp.length+a.O.length*n)*R⟩
  else none

theorem applyMotif_sound {p : PartialMachine} {a : Motif} (ha : a.Valid p) (n : Nat) {z z' : PZ}
    (h : applyMotif a n z = some z') : prun p (a.k*n) z = some z' := by
  obtain ⟨hi,ho,ha⟩ := ha
  cases hr : a.right
  · simp [applyMotif,hr] at h
    obtain ⟨⟨⟨hq,hmodl⟩,hmodr⟩,hout⟩ := h
    have hl := Nat.mod_add_div z.l (2^(a.lp.length+a.I.length*n))
    have hh := Nat.mod_add_div z.r (2^a.rp.length)
    rw [hmodl,prefRep_eq _ _ _ hi] at hl
    rw [hmodr] at hh
    have hs : pzip a.q (a.lp++rep a.I n) a.rp (z.l/2^(a.lp.length+a.I.length*n)) (z.r/2^a.rp.length) = z := by
      cases z; simp only [pzip,prepend,List.length_append,rep_len] at *
      congr <;> omega
    have one := ha
    simp only [hr,Bool.false_eq_true,ite_false] at one
    have hp := psweepL p a.q a.lp a.rp a.I a.O a.k one n (z.l/2^(a.lp.length+a.I.length*n)) (z.r/2^a.rp.length)
    rw [hs] at hp
    rw [hp,← hout]
    simp only [pzip,prepend,List.length_append,rep_len,prefRep_eq _ _ _ ho]
  · simp [applyMotif,hr] at h
    obtain ⟨⟨⟨hq,hmodl⟩,hmodr⟩,hout⟩ := h
    have hl := Nat.mod_add_div z.l (2^a.lp.length)
    have hh := Nat.mod_add_div z.r (2^(a.rp.length+a.I.length*n))
    rw [hmodl] at hl
    rw [hmodr,prefRep_eq _ _ _ hi] at hh
    have hs : pzip a.q a.lp (a.rp++rep a.I n) (z.l/2^a.lp.length) (z.r/2^(a.rp.length+a.I.length*n)) = z := by
      cases z; simp only [pzip,prepend,List.length_append,rep_len] at *
      congr <;> omega
    have one := ha
    simp only [hr,ite_true] at one
    have hp := psweepR p a.q a.lp a.rp a.I a.O a.k one n (z.l/2^a.lp.length) (z.r/2^(a.rp.length+a.I.length*n))
    rw [hs] at hp
    rw [hp,← hout]
    simp only [pzip,prepend,List.length_append,rep_len,prefRep_eq _ _ _ ho]

#print axioms applyMotif_sound
end BB6Coverage.Agent29PackedRun

namespace BB6Coverage.Agent29PackedRun
open BB6Coverage
inductive Action (p : PartialMachine) where
  | prim (n : Nat)
  | sweep (a : Motif) (h : a.Valid p) (n : Nat)

def Action.cost {p : PartialMachine} : Action p → Nat
  | .prim n => n
  | .sweep a _ n => a.k*n

def Action.run {p : PartialMachine} (a : Action p) (z : PZ) : Option PZ :=
  match a with
  | .prim n => prun p n z
  | .sweep m _ n => applyMotif m n z

theorem Action.sound {p : PartialMachine} (a : Action p) (z z' : PZ) (h : a.run z = some z') :
    prun p a.cost z = some z' := by
  cases a with
  | prim n => exact h
  | sweep m hm n => exact applyMotif_sound hm n h

def actionsCost {p : PartialMachine} : List (Action p) → Nat
  | [] => 0
  | a::as => a.cost + actionsCost as

def runActions {p : PartialMachine} : List (Action p) → PZ → Option PZ
  | [],z => some z
  | a::as,z => (a.run z).bind (runActions as)

theorem runActions_sound {p : PartialMachine} (as : List (Action p)) (z z' : PZ)
    (h : runActions as z = some z') : prun p (actionsCost as) z = some z' := by
  induction as generalizing z with
  | nil => exact h
  | cons a as ih =>
    cases he : a.run z with
    | none => simp [runActions,he] at h
    | some w =>
      have h' : runActions as w = some z' := by simpa [runActions,he] using h
      exact pjoin (a.sound z w he) (ih w h')

#print axioms runActions_sound
end BB6Coverage.Agent29PackedRun
