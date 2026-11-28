import FiniteHalting
import GenericClosedGraph

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw34Plan
open BB6Coverage BB6Coverage.Agent50SideCycle

/-! Literal source split tree: each internal node checks every source
transition choice and freshness; each residual must equal its explicit
source table. No numerical mass claim is used for exhaustiveness. -/

def slots : List Slot := (List.finRange 6).flatMap fun q => [(q,false),(q,true)]

theorem slots_complete (s : Slot) : s ∈ slots := by
  rcases s with ⟨q,b⟩
  apply List.mem_flatMap.mpr
  refine ⟨q,List.mem_finRange q,?_⟩
  cases b <;> simp

def moves : List Move :=
  [false,true].flatMap fun w =>
    [false,true].flatMap fun r =>
      (List.finRange 6).map fun q => ⟨w,r,q⟩

def table (codes : List Nat) : PartialMachine := fun s =>
  let code := (codes[2*s.1.val+s.2.toNat]?).getD 0
  if code = 0 then none
  else if code = 1 then some none
  else (moves[code-2]?).map some

def sameTable (p q : PartialMachine) : Bool :=
  slots.all fun s => decide (p s = q s)

theorem sameTable_sound (p q : PartialMachine) (h : sameTable p q = true) : p = q := by
  funext s
  exact of_decide_eq_true (List.all_eq_true.mp h s (slots_complete s))

def closedCheck (p : PartialMachine) (ss : List (Fin 6)) : Bool :=
  ss.all fun q => [false,true].all fun b =>
    match p (q,b) with
    | some (some mv) => ss.contains mv.next
    | _ => false

theorem closedCheck_sound (p : PartialMachine) (ss : List (Fin 6))
    (h : closedCheck p ss = true) :
    BB6.Agent50GenericClosedGraph.Closed p (fun q => q ∈ ss) := by
  intro q b hq
  have hb : b ∈ [false,true] := by cases b <;> simp
  have ht := List.all_eq_true.mp (List.all_eq_true.mp h q hq) b hb
  cases hp : p (q,b) with
  | none => simp [hp] at ht
  | some t =>
    cases t with
    | none => simp [hp] at ht
    | some mv =>
      exact ⟨mv,rfl,List.contains_iff_mem.mp (by simpa [hp] using ht)⟩

inductive Cert where
  | halt (n : Nat)
  | side (entry period : Nat) (right : Bool) (boundary : Int)
  | closed (entry : Nat) (ss : List (Fin 6))

def certCheck (bound : Nat) (p : PartialMachine) : Cert → Bool
  | .halt n => decide (n+1 ≤ bound) && finiteHaltCheck p n
  | .side entry period right boundary =>
      decide (0 < period) && fastSideCycleCheck p entry period right boundary
  | .closed entry ss =>
      match finitePartialRun p entry finiteBlank with
      | none => false
      | some c => ss.contains c.state && closedCheck p ss

theorem cert_sound (bound : Nat) (p : PartialMachine) (cert : Cert)
    (h : certCheck bound p cert = true) : Cover (DecidedBelow bound) p := by
  cases cert with
  | halt n =>
    have hh : decide (n+1 ≤ bound) = true ∧ finiteHaltCheck p n = true := by
      simpa only [certCheck,Bool.and_eq_true] using h
    exact finiteHaltCheck_sound p n bound (of_decide_eq_true hh.1) hh.2
  | side entry period right boundary =>
    have hh : decide (0 < period) = true ∧
        fastSideCycleCheck p entry period right boundary = true := by
      simpa only [certCheck,Bool.and_eq_true] using h
    apply Cover.leaf
    intro m hm
    exact Or.inl (fastSideCycleCheck_sound p entry period right boundary
      (of_decide_eq_true hh.1) hh.2 m hm)
  | closed entry ss =>
    cases he : finitePartialRun p entry finiteBlank with
    | none => simp [certCheck,he] at h
    | some c =>
      have hh : ss.contains c.state = true ∧ closedCheck p ss = true := by
        simpa only [certCheck,he,Bool.and_eq_true] using h
      apply Cover.leaf
      intro m hm
      have hr : run m entry blank = some (embedFinRay c) := by
        simpa only [embedFinRay_blank] using
          finitePartialRun_sound p m hm finiteBlank c entry he
      exact Or.inl (BB6.Agent50GenericClosedGraph.never_after p
        (fun q => q ∈ ss) (closedCheck_sound p ss hh.2) m hm entry
        (embedFinRay c) hr (List.contains_iff_mem.mp hh.1))

inductive PlanNode (α : Type) where
  | leaf (cert : α)
  | residual (row : Nat)
  | split (slot : Slot) (children : List Nat)

abbrev Node := PlanNode Cert

def checkWith {α : Type} (nodes : Array (PlanNode α)) (rows : List (List Nat))
    (verify : PartialMachine → α → Bool) :
    Nat → Nat → PartialMachine → Bool
  | 0, _, _ => false
  | k+1, i, p =>
      match nodes[i]? with
      | none => false
      | some (.leaf cert) => verify p cert
      | some (.residual j) =>
          match rows[j]? with
          | none => false
          | some row => sameTable p (table row)
      | some (.split s children) =>
          decide (p s = none) && decide (children.length = choices.length) &&
          choices.all fun t =>
            match children[choices.idxOf t]? with
            | none => false
            | some j => checkWith nodes rows verify k j (refine p s t)

theorem checkWith_sound {α : Type} (nodes : Array (PlanNode α)) (rows : List (List Nat))
    {good : Machine → Prop} (verify : PartialMachine → α → Bool)
    (leaf_sound : ∀ p cert, verify p cert = true → Cover good p)
    (hrows : ∀ (j : Nat) (row : List Nat), rows[j]? = some row → Cover good (table row))
    (fuel i : Nat) (p : PartialMachine) (h : checkWith nodes rows verify fuel i p = true) :
    Cover good p := by
  induction fuel generalizing i p with
  | zero => simp [checkWith] at h
  | succ k ih =>
    cases hn : nodes[i]? with
    | none => simp [checkWith,hn] at h
    | some node =>
      cases node with
      | leaf cert =>
        have hc : verify p cert = true := by simpa only [checkWith,hn] using h
        exact leaf_sound p cert hc
      | residual j =>
        cases hr : rows[j]? with
        | none => simp [checkWith,hn,hr] at h
        | some row =>
          have he : sameTable p (table row) = true := by simpa only [checkWith,hn,hr] using h
          rw [sameTable_sound p (table row) he]
          exact hrows j row hr
      | split s children =>
        have hh : (decide (p s = none) = true ∧ decide (children.length = choices.length) = true) ∧
            (choices.all fun t =>
              match children[choices.idxOf t]? with
              | none => false
              | some j => checkWith nodes rows verify k j (refine p s t)) = true := by
          simpa only [checkWith,hn,Bool.and_eq_true] using h
        apply Cover.branch p s (of_decide_eq_true hh.1.1)
        intro t ht
        have htcheck := List.all_eq_true.mp hh.2 t ht
        cases hj : children[choices.idxOf t]? with
        | none => simp [hj] at htcheck
        | some j =>
          exact ih j (refine p s t) (by simpa only [hj] using htcheck)

def check (nodes : Array Node) (rows : List (List Nat)) (bound : Nat) :=
  checkWith nodes rows (certCheck bound)

theorem check_sound (nodes : Array Node) (rows : List (List Nat)) (bound : Nat)
    {good : Machine → Prop} (lift : ∀ m, DecidedBelow bound m → good m)
    (hrows : ∀ (j : Nat) (row : List Nat), rows[j]? = some row → Cover good (table row))
    (fuel i : Nat) (p : PartialMachine) (h : check nodes rows bound fuel i p = true) :
    Cover good p := by
  apply checkWith_sound nodes rows (certCheck bound) _ hrows fuel i p h
  intro q c hc
  exact .leaf q (fun m hm => lift m ((cert_sound bound q c hc).sound m hm))

theorem check_closed (nodes : Array Node) (bound fuel root : Nat) (p : PartialMachine)
    (h : check nodes [] bound fuel root p = true) : Cover (DecidedBelow bound) p := by
  apply check_sound nodes [] bound (fun _ h => h) _ fuel root p h
  intro j row hj
  simp at hj

/-- A machine lies in one of the literal residual cylinders stored by a plan.
The index/equality witness deliberately preserves the exact source row rather
than reducing the residual to an external cardinality. -/
def ExplicitResidual (rows : List (List Nat)) (m : Machine) : Prop :=
  ∃ (j : Nat) (row : List Nat),
    rows[j]? = some row ∧ compatible (table row) m

/-- A checked plan with residual leaves is an exact source-level cover by
bounded/nonhalting certificates or one of its explicit residual cylinders. -/
theorem check_explicit_residual
    (nodes : Array Node) (rows : List (List Nat)) (bound fuel root : Nat)
    (p : PartialMachine) (h : check nodes rows bound fuel root p = true) :
    Cover (fun m => DecidedBelow bound m ∨ ExplicitResidual rows m) p := by
  apply check_sound nodes rows bound (fun _ hd => Or.inl hd) _ fuel root p h
  intro j row hj
  apply Cover.leaf
  intro m hm
  exact Or.inr ⟨j, row, hj, hm⟩

#print axioms sameTable_sound
#print axioms closedCheck_sound
#print axioms cert_sound
#print axioms checkWith_sound
#print axioms check_sound
#print axioms check_closed
#print axioms check_explicit_residual
end BB6.Agent50Raw34Plan
