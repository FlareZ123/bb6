import Raw40Exceptional28
import Raw40A0LABase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent42Raw40ExceptionalA0LALift
open BB6Coverage
open BB6.Agent42Raw40Exceptional28

/-- Finite proof certificate that every source-assigned transition of p
    appears unchanged in q. No assumptions about unassigned transitions. -/
def extendsCheck (p q : PartialMachine) : Bool :=
  (List.finRange 6).all fun s =>
    ([false,true] : List Bool).all fun b =>
      match p (s,b) with
      | none => true
      | some t => decide (q (s,b) = some t)

theorem extends_sound (p q : PartialMachine) (hc : extendsCheck p q = true)
    (m : Machine) (hq : compatible q m) : compatible p m := by
  intro s t hs
  rcases s with ⟨a,b⟩
  have ha := List.all_eq_true.mp hc a (List.mem_finRange a)
  have hb : b ∈ ([false,true] : List Bool) := by cases b <;> simp
  have hs' := List.all_eq_true.mp ha b hb
  have he : q (a,b) = some t := by simpa [extendsCheck,hs] using hs'
  exact hq (a,b) t he

/-- Every one of the 28 independently nonhalting source cylinders
    lies inside the actual six-hole A1=0LA Raw40 parent. -/
theorem literal_parent_checks : bank.all
    (extendsCheck BB6.Agent19Raw40.A0LA.p) = true := by decide +kernel

theorem source_lives_in_parent (q : PartialMachine) (hq : q ∈ bank)
    (m : Machine) (hm : compatible q m) :
    compatible BB6.Agent19Raw40.A0LA.p m := by
  have hc := List.all_eq_true.mp literal_parent_checks q hq
  exact extends_sound _ q hc m hm

/-- These are actual original-source never-halting subfamilies of the
    still-open six-hole Raw40 parent, not unrelated table cylinders.
    This does not assert that their union exhausts the parent. -/
theorem parent_subbank_certificate :
    ∀ q ∈ bank, ∀ m : Machine, compatible q m →
      compatible BB6.Agent19Raw40.A0LA.p m ∧ NeverHalts m := by
  intro q hq m hm
  exact ⟨source_lives_in_parent q hq m hm, all_never q hq m hm⟩

#print axioms parent_subbank_certificate
end BB6.Agent42Raw40ExceptionalA0LALift
