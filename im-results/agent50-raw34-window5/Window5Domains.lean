import Window5General
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Window5Domains
open BB6Coverage BB6.Agent50Window5

/-!
A broad radius-two Raw34 closed-window family. An action is permitted
if its state/symbol slot is absent from the invariant, or if its
ordinary move sends *every* supported 5-cell neighborhood to another
supported neighborhood for BOTH arbitrary incoming tape bits.

The source checker operates on original total machines. It therefore
protects genuinely HALT-assigned instructions at unreachable slots.
-/

def Permitted
    (P : Fin 6 → Bool → Bool → Bool → Bool → Bool → Bool)
    (q : Fin 6) (c : Bool) (a : Option Move) : Prop :=
  (∀ l2 l1 r1 r2, P q l2 l1 c r1 r2 = false) ∨
  match a with
  | none => False
  | some mv =>
      ∀ l2 l1 r1 r2 incoming,
        P q l2 l1 c r1 r2 = true →
        successor5 P mv l2 l1 r1 r2 incoming = true

/-- Generalization from a sparse fixed-source table to the maximal
per-invariant Cartesian product of allowed physical transitions. -/
theorem never_of_permitted
    (P : Fin 6 → Bool → Bool → Bool → Bool → Bool → Bool)
    (m : Machine)
    (hstart : P 0 false false false false false = true)
    (hsafe : ∀ q c, Permitted P q c (m (q,c))) : NeverHalts m := by
  let p : PartialMachine := fun s => some (m s)
  have hlocal : LocalOK p P := by
    intro q l2 l1 c r1 r2 hp
    rcases hsafe q c with hmissing | hallowed
    · have hcontra := hmissing l2 l1 r1 r2
      rw [hp] at hcontra
      cases hcontra
    · cases hrow : m (q,c) with
      | none => simp [hrow] at hallowed
      | some mv =>
        have hs :
            ∀ l2 l1 r1 r2 incoming,
              P q l2 l1 c r1 r2 = true →
              successor5 P mv l2 l1 r1 r2 incoming = true := by
          simpa [hrow] using hallowed
        have hf := hs l2 l1 r1 r2 false hp
        have ht := hs l2 l1 r1 r2 true hp
        simpa [p,hrow] using And.intro hf ht
  have hcompatible : compatible p m := by
    intro s v hv
    exact Option.some.inj hv
  exact never_of_localOK p P hstart hlocal m hcompatible

/-- The radius-two reachable-window mask was obtained by a finite
two-successor BFS. Its soundness is *not* assumed: all machine
families below are justified by the universal theorem above. -/
def invariantMask : Nat :=
  0xf000f000fffffffffffffccccccccfcc00000001

def P : Fin 6 → Bool → Bool → Bool → Bool → Bool → Bool :=
  masked invariantMask

theorem start_checked :
    P 0 false false false false false = true := by
  decide

theorem family_never (m : Machine)
    (h : ∀ q c, Permitted P q c (m (q,c))) :
    NeverHalts m :=
  never_of_permitted P m start_checked h

/-- All 25 distinct physical transitions, including the true HALT,
    are enumerated independently of the abstract invariant. -/
def allMoves : List (Option Move) :=
  [none] ++
    ([false,true] : List Bool).flatMap (fun w =>
      ([false,true] : List Bool).flatMap (fun r =>
        (List.finRange 6).map (fun q => some (⟨w,r,q⟩ : Move))))

def countAt (q : Fin 6) (c : Bool) : Nat :=
  (allMoves.filter (fun a => permittedBoolean P q c a)).length

theorem enumeration_count : allMoves.length = 25 := by decide
theorem enumeration_nodup : allMoves.Nodup := by decide

/-- The root's four authentic assigned rows are permitted. -/
theorem raw34_root_permitted :
    Permitted P 0 false (some ⟨true,true,1⟩) ∧
    Permitted P 1 false (some ⟨true,true,2⟩) ∧
    Permitted P 2 false (some ⟨false,true,3⟩) ∧
    Permitted P 3 false (some ⟨true,false,2⟩) := by
  decide

/-- Exactly computed source-side slot cardinalities in physical
25-choice semantics (D1,C1,B1,A1,E0,E1,F0,F1). All four
original-root slots are held fixed, not varied. -/
theorem counts_exact :
    countAt 3 true = 6 ∧
    countAt 2 true = 6 ∧
    countAt 1 true = 8 ∧
    countAt 0 true = 25 ∧
    countAt 4 false = 25 ∧
    countAt 4 true = 8 ∧
    countAt 5 false = 25 ∧
    countAt 5 true = 25 := by
  decide

theorem physical_product_cardinality :
    6 * 6 * 8 * 25 * 25 * 8 * 25 * 25 = (900000000 : Nat) := by
  decide

#print axioms never_of_permitted
#print axioms family_never
#print axioms enumeration_count
#print axioms enumeration_nodup
#print axioms raw34_root_permitted
#print axioms counts_exact
#print axioms physical_product_cardinality
end BB6.Agent50Window5Domains
