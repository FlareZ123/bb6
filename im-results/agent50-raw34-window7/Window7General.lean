import Window5Domains
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Window7
open BB6Coverage BB429WindowR4 BB429WindowLeaf

/-!
An original, unbounded, infinite-tape radius-three (seven physical
cell) finite-observation proof rule. A local abstract successor has
two branches for the tape cell newly revealed at distance four.
All local invariants are interpreted on the actual two-way infinite
tape, not a finite simulation.
-/

def lift7
    (P : Fin 6 → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool)
    (q : Fin 6) (w : W) : Bool :=
  P q w.l3 w.l2 w.l1 w.c w.r1 w.r2 w.r3

def successor7
    (P : Fin 6 → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool)
    (mv : Move) (l3 l2 l1 r1 r2 r3 entering : Bool) : Bool :=
  P mv.next
    (if mv.right then l2 else entering)
    (if mv.right then l1 else l3)
    (if mv.right then mv.write else l2)
    (if mv.right then r1 else l1)
    (if mv.right then r2 else mv.write)
    (if mv.right then r3 else r1)
    (if mv.right then entering else r2)

def LocalOK7 (p : PartialMachine)
    (P : Fin 6 → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool) : Prop :=
  ∀ q (l3 l2 l1 c r1 r2 r3 : Bool),
    P q l3 l2 l1 c r1 r2 r3 = true →
    match p (q,c) with
    | some (some mv) =>
        successor7 P mv l3 l2 l1 r1 r2 r3 false = true ∧
        successor7 P mv l3 l2 l1 r1 r2 r3 true = true
    | _ => False

theorem localOK7_step (p : PartialMachine)
    (P : Fin 6 → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool)
    (h : LocalOK7 p P) :
    ∀ q l3 l2 l1 c r1 r2 r3,
      P q l3 l2 l1 c r1 r2 r3 = true →
      ∃ mv, p (q,c) = some (some mv) ∧
        ∀ entering, successor7 P mv l3 l2 l1 r1 r2 r3 entering = true := by
  intro q l3 l2 l1 c r1 r2 r3 hp
  have hs := h q l3 l2 l1 c r1 r2 r3 hp
  cases hrow : p (q,c) with
  | none => simp [hrow] at hs
  | some opt =>
    cases opt with
    | none => simp [hrow] at hs
    | some mv =>
      have hb :
          successor7 P mv l3 l2 l1 r1 r2 r3 false = true ∧
          successor7 P mv l3 l2 l1 r1 r2 r3 true = true := by
        simpa [hrow] using hs
      refine ⟨mv, rfl, ?_⟩
      intro entering
      cases entering with
      | false => exact hb.1
      | true => exact hb.2

/-- A source theorem: ALL physical original-tape completions of an
inductively closed seven-cell partial-machine predicate never halt,
including HALT on an abstractly unreachable transition slot. -/
theorem never_of_localOK7
    (p : PartialMachine)
    (P : Fin 6 → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool)
    (hstart : P 0 false false false false false false false = true)
    (hlocal : LocalOK7 p P)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have h0 : lift7 P blank.state (view blank) = true := by
    simpa [lift7, view, blank] using hstart
  have hfixed : ∀ q w, lift7 P q w = true →
      ∃ mv, p (q,w.c) = some (some mv) := by
    intro q w hp
    obtain ⟨mv, hrow, _⟩ :=
      localOK7_step p P hlocal q w.l3 w.l2 w.l1 w.c w.r1 w.r2 w.r3 hp
    exact ⟨mv, hrow⟩
  have hclosed : ∀ q w far mv, lift7 P q w = true →
      p (q,w.c) = some (some mv) →
      lift7 P mv.next
        (if mv.right then shiftR w mv.write far
         else shiftL w mv.write far) = true := by
    intro q w far mv hp hrow
    obtain ⟨mv0,hrow0,hs⟩ :=
      localOK7_step p P hlocal q w.l3 w.l2 w.l1 w.c w.r1 w.r2 w.r3 hp
    have heq : mv0 = mv :=
      Option.some.inj (Option.some.inj (hrow0.symm.trans hrow))
    subst mv0
    cases hr : mv.right with
    | false =>
      have hmove := hs w.l4
      simpa [lift7, successor7, shiftL, hr] using hmove
    | true =>
      have hmove := hs w.r4
      simpa [lift7, successor7, shiftR, hr] using hmove
  exact partial_finite_window_never p (lift7 P)
    h0 hfixed hclosed m hm

def masked7 (bits : Nat) (q : Fin 6)
    (l3 l2 l1 c r1 r2 r3 : Bool) : Bool :=
  bits.testBit (128*q.val + 64*l3.toNat + 32*l2.toNat +
    16*l1.toNat + 8*c.toNat + 4*r1.toNat +
    2*r2.toNat + r3.toNat)

def Permitted7
    (P : Fin 6 → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool)
    (q : Fin 6) (c : Bool) (a : Option Move) : Prop :=
  (∀ l3 l2 l1 r1 r2 r3,
      P q l3 l2 l1 c r1 r2 r3 = false) ∨
  match a with
  | none => False
  | some mv =>
      ∀ l3 l2 l1 r1 r2 r3 entering,
        P q l3 l2 l1 c r1 r2 r3 = true →
        successor7 P mv l3 l2 l1 r1 r2 r3 entering = true

/-- All seven-cell finite-action propositions remain constructively
decidable; the physical action must first be pattern matched. -/
def permitted7Decidable
    (P : Fin 6 → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool)
    (q : Fin 6) (c : Bool) (a : Option Move) :
    Decidable (Permitted7 P q c a) := by
  cases a with
  | none =>
    unfold Permitted7
    infer_instance
  | some mv =>
    unfold Permitted7
    infer_instance

instance permitted7Instance
    (P : Fin 6 → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool)
    (q : Fin 6) (c : Bool) (a : Option Move) :
    Decidable (Permitted7 P q c a) :=
  permitted7Decidable P q c a

def permitted7Bool
    (P : Fin 6 → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool)
    (q : Fin 6) (c : Bool) (a : Option Move) : Bool :=
  decide (Permitted7 P q c a)

/-- Original infinite blank-tape theorem for arbitrary total machines
whose physical actions belong to the permitted radius-three domains. -/
theorem never_of_permitted7
    (P : Fin 6 → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool)
    (m : Machine)
    (hstart : P 0 false false false false false false false = true)
    (hsafe : ∀ q c, Permitted7 P q c (m (q,c))) : NeverHalts m := by
  let p : PartialMachine := fun s => some (m s)
  have hlocal : LocalOK7 p P := by
    intro q l3 l2 l1 c r1 r2 r3 hp
    rcases hsafe q c with hmissing | hallowed
    · have hcontra := hmissing l3 l2 l1 r1 r2 r3
      rw [hp] at hcontra
      cases hcontra
    · cases hrow : m (q,c) with
      | none => simp [hrow] at hallowed
      | some mv =>
        have hs :
            ∀ l3 l2 l1 r1 r2 r3 entering,
              P q l3 l2 l1 c r1 r2 r3 = true →
              successor7 P mv l3 l2 l1 r1 r2 r3 entering = true := by
          simpa [hrow] using hallowed
        have hf := hs l3 l2 l1 r1 r2 r3 false hp
        have ht := hs l3 l2 l1 r1 r2 r3 true hp
        simpa [p,hrow] using And.intro hf ht
  have hcompatible : compatible p m := by
    intro s v hv
    exact Option.some.inj hv
  exact never_of_localOK7 p P hstart hlocal m hcompatible

#print axioms never_of_localOK7
#print axioms never_of_permitted7
end BB6.Agent50Window7
