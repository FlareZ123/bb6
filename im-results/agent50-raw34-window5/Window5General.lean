import WindowLeaf
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Window5
open BB6Coverage BB429WindowR4 BB429WindowLeaf

/-!
Sound radius-two local tape-window certificates for a sparse original
six-state binary machine. All five inspected cells are physical tape cells.
Both values of the freshly exposed sixth cell are quantified; no blank-tail
assumption is made. In particular a machine may have a literal HALT
instruction on an unreachable slot.
-/

/-- Extract the actual five central tape cells from the source-proved
nine-cell observation. -/
def lift5 (P : Fin 6 → Bool → Bool → Bool → Bool → Bool → Bool)
    (q : Fin 6) (w : W) : Bool :=
  P q w.l2 w.l1 w.c w.r1 w.r2

/-- One exact radius-two successor for arbitrary outside symbol. -/
def successor5 (P : Fin 6 → Bool → Bool → Bool → Bool → Bool → Bool)
    (v : Move) (l2 l1 r1 r2 incoming : Bool) : Bool :=
  P v.next
    (if v.right then l1 else incoming)
    (if v.right then v.write else l2)
    (if v.right then r1 else l1)
    (if v.right then r2 else v.write)
    (if v.right then incoming else r1)

/-- Boolean finite-local certificate: every permitted five-cell
observation queries an assigned nonhalting instruction whose two
abstract successors satisfy the invariant. -/
def LocalOK (p : PartialMachine)
    (P : Fin 6 → Bool → Bool → Bool → Bool → Bool → Bool) : Prop :=
  ∀ q (l2 l1 c r1 r2 : Bool),
    P q l2 l1 c r1 r2 = true →
    match p (q,c) with
    | some (some mv) =>
        successor5 P mv l2 l1 r1 r2 false = true ∧
        successor5 P mv l2 l1 r1 r2 true = true
    | _ => False

theorem localOK_step (p : PartialMachine)
    (P : Fin 6 → Bool → Bool → Bool → Bool → Bool → Bool)
    (h : LocalOK p P) :
    ∀ q l2 l1 c r1 r2,
      P q l2 l1 c r1 r2 = true →
      ∃ mv, p (q,c) = some (some mv) ∧
        ∀ incoming, successor5 P mv l2 l1 r1 r2 incoming = true := by
  intro q l2 l1 c r1 r2 hp
  have hs := h q l2 l1 c r1 r2 hp
  cases hrow : p (q,c) with
  | none => simp [hrow] at hs
  | some opt =>
    cases opt with
    | none => simp [hrow] at hs
    | some mv =>
      have hb :
          successor5 P mv l2 l1 r1 r2 false = true ∧
          successor5 P mv l2 l1 r1 r2 true = true := by
        simpa [hrow] using hs
      refine ⟨mv, rfl, ?_⟩
      intro incoming
      cases incoming with
      | false => exact hb.1
      | true => exact hb.2

/-- A kernel-checked local finite predicate gives all-time nonhalting
of EVERY physical total completion, including arbitrary HALT rows.
This theorem is about the original infinite tape, not a bounded replay. -/
theorem never_of_localOK
    (p : PartialMachine)
    (P : Fin 6 → Bool → Bool → Bool → Bool → Bool → Bool)
    (hstart : P 0 false false false false false = true)
    (hlocal : LocalOK p P)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have h0 : lift5 P blank.state (view blank) = true := by
    simpa [lift5, view, blank] using hstart
  have hfixed : ∀ q w, lift5 P q w = true →
      ∃ mv, p (q,w.c) = some (some mv) := by
    intro q w hp
    obtain ⟨mv, hrow, _⟩ :=
      localOK_step p P hlocal q w.l2 w.l1 w.c w.r1 w.r2 hp
    exact ⟨mv, hrow⟩
  have hclosed : ∀ q w far mv, lift5 P q w = true →
      p (q,w.c) = some (some mv) →
      lift5 P mv.next
        (if mv.right then shiftR w mv.write far
         else shiftL w mv.write far) = true := by
    intro q w far mv hp hrow
    obtain ⟨mv0,hrow0,hs⟩ :=
      localOK_step p P hlocal q w.l2 w.l1 w.c w.r1 w.r2 hp
    have heq : mv0 = mv :=
      Option.some.inj (Option.some.inj (hrow0.symm.trans hrow))
    subst mv0
    cases hr : mv.right with
    | false =>
      have hmove := hs w.l3
      simpa [lift5, successor5, shiftL, hr] using hmove
    | true =>
      have hmove := hs w.r3
      simpa [lift5, successor5, shiftR, hr] using hmove
  exact partial_finite_window_never p (lift5 P)
    h0 hfixed hclosed m hm

/-- A convenient exact bitmask encoding of a finite five-cell
invariant. Index order is control, L2, L1, scanned, R1, R2. -/
def masked (bits : Nat) (q : Fin 6)
    (l2 l1 c r1 r2 : Bool) : Bool :=
  bits.testBit (32*q.val + 16*l2.toNat + 8*l1.toNat +
      4*c.toNat + 2*r1.toNat + r2.toNat)

theorem mask_cover (bits : Nat) (p : PartialMachine) (bound : Nat)
    (hstart : masked bits 0 false false false false false = true)
    (hlocal : LocalOK p (masked bits)) :
    Cover (DecidedBelow bound) p := by
  apply Cover.leaf p
  intro m hm
  exact Or.inl (never_of_localOK p (masked bits) hstart hlocal m hm)

#print axioms never_of_localOK
#print axioms mask_cover
end BB6.Agent50Window5
