import PackedZipper
import ZipThreeHoleAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent3PackedCycle
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent50SideCycle
open BB6Coverage.Agent10ZipAudit BB6Coverage.Agent13PackedZipper BB6Coverage.Agent31Pump

structure H where
  p : P
  h : Int
  deriving DecidableEq, Repr

def encH (z : Z) : H := ⟨encode z,z.h⟩

def moveH (mv : Move) (z : H) : H :=
  ⟨moveP mv z.p, if mv.right then z.h+1 else z.h-1⟩

theorem enc_move (mv : Move) (z : Z) : encH (move mv z) = moveH mv (encH z) := by
  unfold encH moveH
  rw [encode_move]
  cases h : mv.right <;> simp [move,h]

def stepH (p : PartialMachine) (z : H) : Option H :=
  ((p (readP z.p)).bind id).map (fun mv => moveH mv z)

theorem enc_step (p : PartialMachine) (z : Z) :
    (step p z).map encH = stepH p (encH z) := by
  unfold step stepH
  change _ = ((p (readP (encode z))).bind id).map _
  rw [encode_read]
  cases h : (p (z.q,z.l.headD false)).bind id with
  | none => rfl
  | some mv => simp [enc_move]

def runH (p : PartialMachine) : Nat → H → Option H
  | 0,z => some z
  | n+1,z => (stepH p z).bind (runH p n)

theorem enc_run (p : PartialMachine) (n : Nat) (z : Z) :
    (zrun p n z).map encH = runH p n (encH z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [zrun,runH,← enc_step]
    cases h : step p z with
    | none => rfl
    | some t => exact ih t

def windowH (p : PartialMachine) (right : Bool) (boundary : Int) : Nat → H → Option H
  | 0,z => some z
  | n+1,z => if side right boundary z.h then (stepH p z).bind (windowH p right boundary n) else none

theorem enc_window (p : PartialMachine) (right : Bool) (boundary : Int) (n : Nat) (z : Z) :
    (zipWindow p right boundary n z).map encH = windowH p right boundary n (encH z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [zipWindow,windowH,← enc_step,show (encH z).h = z.h from rfl]
    split
    · cases h : step p z with
      | none => rfl
      | some t => exact ih t
    · rfl

theorem pack_getD (xs : List Bool) (i : Nat) :
    (pack xs).testBit i = xs.getD i false := by
  induction i generalizing xs with
  | zero =>
    rw [Nat.testBit_zero,pack_head,← headD_getD]
    cases xs.headD false <;> rfl
  | succ i ih =>
    rw [Nat.testBit_succ,pack_tail,ih,getD_tail]

theorem pack_eq_getD {xs ys : List Bool} (h : pack xs = pack ys) (i : Nat) :
    xs.getD i false = ys.getD i false := by
  rw [← pack_getD,← pack_getD,h]

theorem pack_mod_eq_getD {xs ys : List Bool} {k : Nat}
    (h : pack xs % 2^k = pack ys % 2^k) (i : Nat) (hi : i < k) :
    xs.getD i false = ys.getD i false := by
  have H := congrArg (fun n : Nat => n.testBit i) h
  simpa [Nat.testBit_mod_two_pow,hi,pack_getD] using H

def tailH (right : Bool) (boundary : Int) (c d : H) : Bool :=
  decide (c.p.q = d.p.q) && decide (side right 0 (d.h-c.h)) &&
    if right then
      decide (c.p.l % 2^((c.h-boundary).toNat+1) = d.p.l % 2^((c.h-boundary).toNat+1)) &&
      decide (c.p.r = d.p.r)
    else
      decide (c.p.l = d.p.l) &&
      decide (c.p.r % 2^(boundary-c.h).toNat = d.p.r % 2^(boundary-c.h).toNat)

theorem tailH_sound (right : Bool) (boundary : Int) (c d : Z)
    (h : tailH right boundary (encH c) (encH d) = true) :
    side right 0 (d.h-c.h) ∧ TailRel right boundary (d.h-c.h) (embed c) (embed d) := by
  simp only [tailH,encH,encode,Bool.and_eq_true] at h
  refine ⟨of_decide_eq_true h.1.2,of_decide_eq_true h.1.1,?_,?_⟩
  · change d.h = c.h + (d.h-c.h); omega
  · intro x hx
    change atCell d (x+(d.h-c.h)) = atCell c x
    unfold atCell
    have hle : (x+(d.h-c.h) ≤ d.h) ↔ x ≤ c.h := by omega
    have hl : (d.h-(x+(d.h-c.h))).toNat = (c.h-x).toNat := by omega
    have hr : (x+(d.h-c.h)-d.h-1).toNat = (x-c.h-1).toNat := by omega
    simp only [hle,hl,hr]
    cases right with
    | false =>
      simp only [Bool.false_eq_true,ite_false,Bool.and_eq_true] at h
      change x ≤ boundary at hx
      by_cases hx' : x ≤ c.h
      · simp only [hx',ite_true]; exact (pack_eq_getD (of_decide_eq_true h.2.1) _).symm
      · simp only [hx',ite_false]
        have hi : (x-c.h-1).toNat < (boundary-c.h).toNat := by omega
        exact (pack_mod_eq_getD (of_decide_eq_true h.2.2) _ hi).symm
    | true =>
      simp only [ite_true,Bool.and_eq_true] at h
      change boundary ≤ x at hx
      by_cases hx' : x ≤ c.h
      · simp only [hx',ite_true]
        have hi : (c.h-x).toNat < (c.h-boundary).toNat+1 := by omega
        exact (pack_mod_eq_getD (of_decide_eq_true h.2.1) _ hi).symm
      · simp only [hx',ite_false]; exact (pack_eq_getD (of_decide_eq_true h.2.2) _).symm

def startH : H := ⟨startP,0⟩

def cycleH (p : PartialMachine) (entry period : Nat) (right : Bool) (boundary : Int) : Bool :=
  match runH p entry startH with
  | none => false
  | some c => match windowH p right boundary period c with
    | none => false
    | some d => tailH right boundary c d

theorem cycleH_sound (p : PartialMachine) (entry period : Nat) (right : Bool) (boundary : Int)
    (hn : 0 < period) (h : cycleH p entry period right boundary = true) :
    ∀ m, compatible p m → NeverHalts m := by
  unfold cycleH at h
  rw [show startH = encH start from rfl,← enc_run] at h
  cases hc : zrun p entry start with
  | none => simp [hc] at h
  | some c =>
    simp only [hc,Option.map_some,← enc_window] at h
    cases hd : zipWindow p right boundary period c with
    | none => simp [hd] at h
    | some d =>
      have ht : tailH right boundary (encH c) (encH d) = true := by simpa [hd] using h
      obtain ⟨hδ,hrel⟩ := tailH_sound right boundary c d ht
      obtain ⟨hr,hw⟩ := zipWindow_sound p right boundary period c d hd
      intro m hm
      have hstart := zrun_sound p m hm entry start c hc
      rw [start_embed] at hstart
      have hloop := zrun_sound p m hm period c d hr
      apply sideCycle_never m right boundary (d.h-c.h) (embed c) (embed d) entry period hn hδ hstart ?_ hloop hrel
      intro j hj e he
      obtain ⟨z,hz⟩ := zipPrefix p period j c d hr (by omega)
      have ht := zrun_sound p m hm j c z hz
      have heq : e = embed z := Option.some.inj (he.symm.trans ht)
      subst e
      exact hw j hj z hz

#print axioms cycleH_sound
end BB6.Agent3PackedCycle
