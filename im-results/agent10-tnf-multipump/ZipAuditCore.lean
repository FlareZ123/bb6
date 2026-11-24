import ThreeHoleAudit
import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent10ZipAudit
open BB6Coverage Agent50Zipper Agent50SideCycle Agent31Pump BB6.Agent13BlankDelay

/-- Equality of two finite words padded by infinitely many zero cells. -/
def padEq : List Bool → List Bool → Bool
  | [], ys => ys.all (!·)
  | x::xs, [] => !x && padEq xs []
  | x::xs, y::ys => (x == y) && padEq xs ys

theorem zeros_getD (ys : List Bool) (h : ys.all (!·) = true) (i : Nat) : ys.getD i false = false := by
  induction ys generalizing i with
  | nil => simp
  | cons y ys ih =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    cases i with
    | zero => simpa using h.1
    | succ i => simpa only [List.getD_cons_succ] using ih h.2 i

theorem padEq_sound (xs ys : List Bool) (h : padEq xs ys = true) (i : Nat) :
    xs.getD i false = ys.getD i false := by
  induction xs generalizing ys i with
  | nil =>
    simpa only [List.getD_nil] using (zeros_getD ys h i).symm
  | cons x xs ih =>
    cases ys with
    | nil =>
      simp only [padEq, Bool.and_eq_true, Bool.not_eq_true'] at h
      cases i with
      | zero => simpa using h.1
      | succ i => exact ih [] h.2 i
    | cons y ys =>
      simp only [padEq,Bool.and_eq_true,beq_iff_eq] at h
      cases i with
      | zero => simpa using h.1
      | succ i => exact ih ys h.2 i

theorem getD_take_lt (xs : List Bool) (n i : Nat) (h : i < n) :
    (xs.take n).getD i false = xs.getD i false := by
  induction xs generalizing n i with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases i with
      | zero => rfl
      | succ i => simpa only [List.take_succ_cons,List.getD_cons_succ] using ih n i (by omega)

/-- Compare only the retained half-line, in head-relative coordinates. -/
def zipTailEq (right : Bool) (boundary : Int) (c d : Z) : Bool :=
  decide (c.q = d.q) && decide (side right 0 (d.h-c.h)) &&
    if right then padEq (c.l.take ((c.h-boundary).toNat+1)) (d.l.take ((c.h-boundary).toNat+1)) && padEq c.r d.r
    else padEq c.l d.l && padEq (c.r.take (boundary-c.h).toNat) (d.r.take (boundary-c.h).toNat)

theorem zipTailEq_sound (right : Bool) (boundary : Int) (c d : Z)
    (h : zipTailEq right boundary c d = true) :
    side right 0 (d.h-c.h) ∧ TailRel right boundary (d.h-c.h) (embed c) (embed d) := by
  simp only [zipTailEq,Bool.and_eq_true,decide_eq_true_eq] at h
  refine ⟨h.1.2,h.1.1,?_,?_⟩
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
      · simp only [hx',ite_true]; exact (padEq_sound c.l d.l h.2.1 _).symm
      · simp only [hx',ite_false]
        have hi : (x-c.h-1).toNat < (boundary-c.h).toNat := by omega
        have H := padEq_sound (c.r.take (boundary-c.h).toNat) (d.r.take (boundary-c.h).toNat) h.2.2 (x-c.h-1).toNat
        rw [getD_take_lt _ _ _ hi,getD_take_lt _ _ _ hi] at H
        exact H.symm
    | true =>
      simp only [ite_true,Bool.and_eq_true] at h
      change boundary ≤ x at hx
      by_cases hx' : x ≤ c.h
      · simp only [hx',ite_true]
        have hi : (c.h-x).toNat < (c.h-boundary).toNat+1 := by omega
        have H := padEq_sound (c.l.take ((c.h-boundary).toNat+1)) (d.l.take ((c.h-boundary).toNat+1)) h.2.1 (c.h-x).toNat
        rw [getD_take_lt _ _ _ hi,getD_take_lt _ _ _ hi] at H
        exact H.symm
      · simp only [hx',ite_false]; exact (padEq_sound c.r d.r h.2.2 _).symm

/-- Each ordinary step is performed once, with a retained-side test. -/
def zipWindow (p : PartialMachine) (right : Bool) (boundary : Int) : Nat → Z → Option Z
  | 0,z => some z
  | n+1,z => if side right boundary z.h then (step p z).bind (zipWindow p right boundary n) else none

theorem zipWindow_sound (p : PartialMachine) (right : Bool) (boundary : Int)
    (n : Nat) (c d : Z) (h : zipWindow p right boundary n c = some d) :
    zrun p n c = some d ∧ ∀ j < n, ∀ e, zrun p j c = some e → side right boundary e.h := by
  induction n generalizing c d with
  | zero => exact ⟨h,fun j hj => by omega⟩
  | succ n ih =>
    by_cases hs : side right boundary c.h
    · cases hstep : step p c with
      | none => simp [zipWindow,hs,hstep] at h
      | some t =>
        have hh : zipWindow p right boundary n t = some d := by simpa [zipWindow,hs,hstep] using h
        obtain ⟨hr,hw⟩ := ih t d hh
        refine ⟨by simp [zrun,hstep,hr],?_⟩
        intro j hj e he
        cases j with
        | zero =>
          have hc : c = e := Option.some.inj he
          subst e; exact hs
        | succ j =>
          exact hw j (by omega) e (by simpa [zrun,hstep] using he)
    · simp [zipWindow,hs] at h

theorem zipPrefix (p : PartialMachine) (n j : Nat) (c d : Z)
    (h : zrun p n c = some d) (hj : j ≤ n) : ∃ e, zrun p j c = some e := by
  rw [show n=j+(n-j) by omega,zrun_add] at h
  cases he : zrun p j c with
  | none => simp [he] at h
  | some e => exact ⟨e,rfl⟩

def zipCycle (p : PartialMachine) (entry period : Nat) (right : Bool) (boundary : Int) : Bool :=
  match zrun p entry start with
  | none => false
  | some c => match zipWindow p right boundary period c with
    | none => false
    | some d => zipTailEq right boundary c d

theorem zipCycle_sound (p : PartialMachine) (entry period : Nat) (right : Bool) (boundary : Int)
    (hn : 0 < period) (h : zipCycle p entry period right boundary = true) :
    ∀ m, compatible p m → NeverHalts m := by
  cases hc : zrun p entry start with
  | none => simp [zipCycle,hc] at h
  | some c =>
    cases hd : zipWindow p right boundary period c with
    | none => simp [zipCycle,hc,hd] at h
    | some d =>
      have ht : zipTailEq right boundary c d = true := by simpa [zipCycle,hc,hd] using h
      obtain ⟨hδ,hrel⟩ := zipTailEq_sound right boundary c d ht
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

theorem knownStep_embed (p : PartialMachine) (z : Z) :
    knownStep p (embed z) = (step p z).map embed := by
  unfold knownStep step
  rw [read_embed]
  cases h : p (z.q,z.l.headD false) with
  | none => rfl
  | some t =>
    cases t with
    | none => rfl
    | some mv => simp [embed_move]

theorem knownRun_zip (p : PartialMachine) (n : Nat) :
    knownRun p n = (zrun p n start).map embed := by
  induction n with
  | zero => exact congrArg some start_embed.symm
  | succ n ih =>
    rw [knownRun,ih,zrun_add]
    cases h : zrun p n start with
    | none => rfl
    | some z =>
      simp only [Option.map_some,Option.bind_some,knownStep_embed]
      cases hh : step p z <;> simp [zrun,hh]

def zipRead (p : PartialMachine) (n : Nat) : Option Slot :=
  (zrun p n start).map fun z => (z.q,z.l.headD false)

theorem zipRead_eq (p : PartialMachine) (n : Nat) :
    zipRead p n = (knownRun p n).map readSlot := by
  rw [knownRun_zip]
  cases h : zrun p n start with
  | none => simp [zipRead,h]
  | some z => simp [zipRead,h,read_embed]

#print axioms zipTailEq_sound
#print axioms zipWindow_sound
#print axioms zipCycle_sound
#print axioms zipRead_eq
end BB6Coverage.Agent10ZipAudit
