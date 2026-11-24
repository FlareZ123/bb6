import R1Sweep
import TNFPilot

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent47R1Sweep
open BB6Coverage Agent50Zipper

theorem initial_embed : embed start = blank := by
  unfold embed start blank
  congr 1
  funext x
  by_cases hx : x ≤ 0 <;> simp [atCell,hx]

theorem r1_never_variant (useD : Bool) (m : Machine) (hm : compatible (tableVariant useD) m) : NeverHalts m := by
  intro n
  obtain ⟨z,hz⟩ := all_defined_variant (useD:=useD) n
  have H := zrun_sound (tableVariant useD) m hm n start z hz
  rw [initial_embed] at H
  change (run m n blank).isSome = true
  rw [H]
  rfl

theorem r1_never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  r1_never_variant false m hm

#print axioms r1_never_variant
#print axioms r1_never
end BB6Coverage.Agent47R1Sweep

namespace BB6.Agent47R1Certificate
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath BB6.Agent50TNFPilot
open BB6Coverage.Agent47R1Sweep

def scheduleVariant (useD : Bool) : List PathEntry :=
  [(1,(1,false),⟨true,false,2⟩),
   (2,(2,true),⟨false,false,3⟩),
   (3,(3,false),⟨true,false,2⟩),
   (4,(2,false),⟨false,false,4⟩),
   (5,(4,false),⟨false,true,0⟩),
   (7,(1,true),⟨false,true,1⟩),
   (10,(4,true),⟨true,false,5⟩),
   (11,(5,false),⟨true,false,0⟩),
   (49,(0,true),⟨false,false,2⟩),
   (52,(5,true),⟨false,false,if useD then 3 else 1⟩)]

abbrev schedule := scheduleVariant false

abbrev endpointVariant (useD : Bool) : PartialMachine := (pathEnd root 2 (scheduleVariant useD)).1
abbrev endpoint := endpointVariant false

def tableEq (a b : PartialMachine) : Bool :=
  (List.finRange 6).all fun q => [false,true].all fun s => decide (a (q,s) = b (q,s))

theorem tableEq_sound (a b : PartialMachine) (h : tableEq a b = true) : a = b := by
  funext x
  rcases x with ⟨q,bv⟩
  have hq := List.all_eq_true.mp h q (List.mem_finRange q)
  have hb : bv ∈ [false,true] := by cases bv <;> simp
  exact of_decide_eq_true (List.all_eq_true.mp hq bv hb)

theorem endpointVariant_eq (useD : Bool) : endpointVariant useD = tableVariant useD :=
  tableEq_sound _ _ (by cases useD <;> decide)

theorem endpoint_eq : endpoint = table := endpointVariant_eq false

theorem path_to_variant (useD : Bool) : FirstHolePath (tableVariant useD) 6 := by
  have H := pathOK_sound root 2 (scheduleVariant useD) FirstHolePath.root (show pathOK root 2 (scheduleVariant useD) = true by cases useD <;> decide)
  have hc : (pathEnd root 2 (scheduleVariant useD)).2 = 6 := by cases useD <;> decide
  rw [hc] at H
  change FirstHolePath (endpointVariant useD) 6 at H
  rw [endpointVariant_eq] at H
  exact H

theorem path_to_table : FirstHolePath table 6 := path_to_variant false

def certificateVariant (B : Nat) (useD : Bool) : WeightedTNFCertificate B (tableVariant useD) 6 :=
  .nonhalt (by cases useD <;> decide) (support6 _) (by
    rw [← endpointVariant_eq]
    exact pathEnd_nohalt root 2 (scheduleVariant useD) firstOneCylinder_no_assigned_halt) (r1_never_variant useD)

def certificate (B : Nat) : WeightedTNFCertificate B table 6 := certificateVariant B false

#print axioms path_to_variant
#print axioms certificateVariant

#print axioms path_to_table
#print axioms certificate
end BB6.Agent47R1Certificate
