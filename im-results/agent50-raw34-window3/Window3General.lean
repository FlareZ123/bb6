import WindowLeaf
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Window3
open BB6Coverage BB429WindowR4 BB429WindowLeaf

/-!
A genuinely universal tape-sensitive partial-table classification rule.
Any per-state predicate over the actual three cells (left, scanned,
right) defines an inductive certificate if each reachable input slot
has a defined ordinary move preserving that predicate for both
possible incoming far-neighbor tape symbols. A cell arbitrarily far
away is never assumed blank, and full Turing-tape semantics are used.

This theorem is independent of a particular Raw34 table. Finite
predicate-template enumeration and BigInt set-union computations
may reuse it for every source-compatible complete machine.
-/

/-- A 3-cell predicate, projected onto the 9-cell sound abstract
    window of Agent 18. No new assumption about remote tape cells. -/
def lift (P : Fin 6 → Bool → Bool → Bool → Bool)
    (q : Fin 6) (w : W) : Bool :=
  P q w.l1 w.c w.r1

/-- The exact 3-cell abstract successor after one ordinary move.
    Incoming is an *arbitrary* Bool at the newly exposed boundary. -/
def successor (P : Fin 6 → Bool → Bool → Bool → Bool)
    (v : Move) (left right incoming : Bool) : Bool :=
  P v.next
    (if v.right then v.write else incoming)
    (if v.right then right else left)
    (if v.right then incoming else v.write)

/-- A table is locally safe if every actual supported neighborhood has
    an ordinary source instruction, and its resulting neighborhood
    belongs to P for either value of the newly exposed tape cell. -/
def LocallySafe (P : Fin 6 → Bool → Bool → Bool → Bool)
    (m : Machine) : Prop :=
  ∀ q left scanned right, P q left scanned right = true →
    ∃ mv, m (q,scanned) = some mv ∧
      ∀ incoming, successor P mv left right incoming = true

/-- Kernel-level soundness for *every* original two-symbol Turing
    machine and *every* Boolean triple predicate P, uniformly
    over the truly infinite tape. -/
theorem never_of_locally_safe
    (P : Fin 6 → Bool → Bool → Bool → Bool)
    (m : Machine)
    (hstart : P 0 false false false = true)
    (hsafe : LocallySafe P m) : NeverHalts m := by
  have h0 : lift P blank.state (view blank) = true := by
    simpa [lift, view, blank] using hstart
  have hclosed : ∀ q w incoming,
      lift P q w = true →
      (match abstractStep m q w incoming with
       | none => true
       | some after => lift P after.1 after.2) = true := by
    intro q w incoming h
    obtain ⟨mv, hm, hs⟩ := hsafe q w.l1 w.c w.r1 h
    simp only [abstractStep, hm, Option.map_some]
    change lift P mv.next
      (if mv.right then shiftR w mv.write incoming
       else shiftL w mv.write incoming) = true
    cases hr : mv.right with
    | false =>
      have hmove := hs w.l2
      simpa [lift, successor, shiftL, hr] using hmove
    | true =>
      have hmove := hs w.r2
      simpa [lift, successor, shiftR, hr] using hmove
  have hfixed : ∀ q w, lift P q w = true →
      (m (q,w.c)).isSome = true := by
    intro q w h
    obtain ⟨mv,hm,_⟩ := hsafe q w.l1 w.c w.r1 h
    simp [hm]
  exact finite_window_never m (lift P) h0 hclosed hfixed

/-- A convenient slotwise version: symbols absent from a state's
    invariant need not be assigned, while each reachable symbol
    has one fixed ordinary move safe for ALL supported neighbor
    choices and BOTH possible fresh incoming bits. -/
def SlotSafe (P : Fin 6 → Bool → Bool → Bool → Bool)
    (m : Machine) : Prop :=
  ∀ q scanned,
    (∃ left right, P q left scanned right = true) →
    ∃ mv, m (q,scanned) = some mv ∧
      ∀ left right incoming,
        P q left scanned right = true →
          successor P mv left right incoming = true

theorem never_of_slotwise_safe
    (P : Fin 6 → Bool → Bool → Bool → Bool)
    (m : Machine)
    (hstart : P 0 false false false = true)
    (hsafe : SlotSafe P m) : NeverHalts m := by
  apply never_of_locally_safe P m hstart
  intro q left scanned right hp
  obtain ⟨mv,hm,hs⟩ :=
    hsafe q scanned ⟨left,right,hp⟩
  exact ⟨mv,hm,fun incoming => hs left right incoming hp⟩

/-- The exact fourteen neighborhood predicates enumerated by the
    companion finite Raw34 source-combinatorics generator. A tag 0
    excludes a control state; tag 1 imposes no tape restriction.
    All expressions are Boolean and inspect only left/current/right. -/
def pred14 (k : Fin 14) (l c r : Bool) : Bool :=
  match k.val with
  | 0 => false
  | 1 => true
  | 2 => !l
  | 3 => l
  | 4 => !c
  | 5 => c
  | 6 => !r
  | 7 => r
  | 8 => (!c) || l
  | 9 => c || (!l)
  | 10 => (!c) || r
  | 11 => c || (!r)
  | 12 => (!l) || r
  | 13 => l || (!r)
  | _ => false

def tagged (T : Fin 6 → Fin 14) : Fin 6 → Bool → Bool → Bool → Bool :=
  fun q l c r => pred14 (T q) l c r

/-- A source slot is permitted either when *no* observation in its
    state can read this symbol, allowing any HALT action, or when
    it contains an ordinary move preserving the three-cell predicate
    for all possible previous neighbors and fresh incoming symbols.

    The set of such actions is a Cartesian-product constraint on the
    physical twelve-entry complete transition table, justifying the
    finite 25-ary union calculation for each fixed tag vector. -/
def Permitted (T : Fin 6 → Fin 14)
    (q : Fin 6) (scanned : Bool) (action : Option Move) : Prop :=
  (∀ left right, tagged T q left scanned right = false) ∨
    ∃ mv, action = some mv ∧
      ∀ left right incoming,
        tagged T q left scanned right = true →
          successor (tagged T) mv left right incoming = true

/-- Universal soundness for *all* 14^6 tag vectors and all their
    25-choice compatible physical Turing machines. In particular,
    a HALT action at a genuinely unread symbol is harmless. -/
theorem never_of_tagged_permitted
    (T : Fin 6 → Fin 14)
    (m : Machine)
    (hstart : tagged T 0 false false false = true)
    (hallowed : ∀ q scanned, Permitted T q scanned (m (q,scanned))) :
    NeverHalts m := by
  apply never_of_slotwise_safe (tagged T) m hstart
  intro q scanned hreach
  rcases hallowed q scanned with hmiss | ⟨mv,hm,hs⟩
  · obtain ⟨left,right,hobs⟩ := hreach
    have hbad := hmiss left right
    rw [hobs] at hbad
    cases hbad
  · exact ⟨mv,hm,hs⟩

#print axioms never_of_locally_safe
#print axioms never_of_slotwise_safe
#print axioms never_of_tagged_permitted
end BB6.Agent50Window3
