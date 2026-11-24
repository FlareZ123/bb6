import R1Pumps
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

theorem never_of_defined (action : Move)
    (hd : ∀ n, ∃ z, zrun (tableWith action) n start = some z)
    (m : Machine) (hm : compatible (tableWith action) m) : NeverHalts m := by
  intro n
  obtain ⟨z,hz⟩ := hd n
  have H := zrun_sound (tableWith action) m hm n start z hz
  rw [initial_embed] at H
  change (run m n blank).isSome = true
  rw [H]
  rfl

theorem r1_never_variant (useD : Bool) (m : Machine) (hm : compatible (tableVariant useD) m) : NeverHalts m :=
  never_of_defined (zeroBD useD) (all_defined_variant (useD:=useD)) m hm

theorem r1_never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  r1_never_variant false m hm

#print axioms r1_never_variant
#print axioms r1_never
end BB6Coverage.Agent47R1Sweep

namespace BB6.Agent47R1Certificate
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath BB6.Agent50TNFPilot
open BB6Coverage.Agent47R1Sweep

def scheduleAction (action : Move) : List PathEntry :=
  [(1,(1,false),⟨true,false,2⟩),
   (2,(2,true),⟨false,false,3⟩),
   (3,(3,false),⟨true,false,2⟩),
   (4,(2,false),⟨false,false,4⟩),
   (5,(4,false),⟨false,true,0⟩),
   (7,(1,true),⟨false,true,1⟩),
   (10,(4,true),⟨true,false,5⟩),
   (11,(5,false),⟨true,false,0⟩),
   (49,(0,true),⟨false,false,2⟩),
   (52,(5,true),action)]

abbrev scheduleVariant (useD : Bool) := scheduleAction (zeroBD useD)

abbrev schedule := scheduleVariant false

abbrev endpointAction (action : Move) : PartialMachine := (pathEnd root 2 (scheduleAction action)).1
abbrev endpointVariant (useD : Bool) : PartialMachine := endpointAction (zeroBD useD)
abbrev endpoint := endpointVariant false

def tableEq (a b : PartialMachine) : Bool :=
  (List.finRange 6).all fun q => [false,true].all fun s => decide (a (q,s) = b (q,s))

theorem tableEq_sound (a b : PartialMachine) (h : tableEq a b = true) : a = b := by
  funext x
  rcases x with ⟨q,bv⟩
  have hq := List.all_eq_true.mp h q (List.mem_finRange q)
  have hb : bv ∈ [false,true] := by cases bv <;> simp
  exact of_decide_eq_true (List.all_eq_true.mp hq bv hb)

def actionCheck (action : Move) : Bool :=
  tableEq (endpointAction action) (tableWith action) &&
  (pathOK root 2 (scheduleAction action) &&
   decide ((pathEnd root 2 (scheduleAction action)).2 = 6))

def allActionCheck : Bool :=
  (List.finRange 6).all fun q => [false,true].all fun w =>
    [false,true].all fun r => actionCheck ⟨w,r,q⟩

theorem all_actions_checked : allActionCheck = true := by decide

theorem action_checked (action : Move) : actionCheck action = true := by
  rcases action with ⟨w,r,q⟩
  have hq := List.all_eq_true.mp all_actions_checked q (List.mem_finRange q)
  have hw : w ∈ [false,true] := by cases w <;> simp
  have hr : r ∈ [false,true] := by cases r <;> simp
  exact List.all_eq_true.mp (List.all_eq_true.mp hq w hw) r hr

theorem action_checked_parts (action : Move) :
    tableEq (endpointAction action) (tableWith action) = true ∧
    pathOK root 2 (scheduleAction action) = true ∧
    (pathEnd root 2 (scheduleAction action)).2 = 6 := by
  simpa only [actionCheck,Bool.and_eq_true,decide_eq_true_eq] using action_checked action

theorem endpointAction_eq (action : Move) : endpointAction action = tableWith action :=
  tableEq_sound _ _ (action_checked_parts action).1

theorem path_to_action (action : Move) : FirstHolePath (tableWith action) 6 := by
  have H := pathOK_sound root 2 (scheduleAction action) FirstHolePath.root (action_checked_parts action).2.1
  rw [(action_checked_parts action).2.2] at H
  change FirstHolePath (endpointAction action) 6 at H
  rw [endpointAction_eq] at H
  exact H

def certificateAction (B : Nat) (action : Move)
    (hd : ∀ n, ∃ z, BB6Coverage.Agent50Zipper.zrun (tableWith action) n start = some z) :
    WeightedTNFCertificate B (tableWith action) 6 :=
  .nonhalt (by rfl) (support6 _) (by
    rw [← endpointAction_eq]
    exact pathEnd_nohalt root 2 (scheduleAction action) firstOneCylinder_no_assigned_halt)
    (never_of_defined action hd)

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

def certificateRA (B : Nat) : WeightedTNFCertificate B (tableWith zeroRA) 6 :=
  certificateAction B zeroRA all_defined_RA

def certificateOneBD (B : Nat) (useD : Bool) : WeightedTNFCertificate B (tableWith (oneBD useD)) 6 :=
  certificateAction B (oneBD useD) (all_defined_BD useD)

def certificateLC (B : Nat) : WeightedTNFCertificate B (tableWith oneLC) 6 :=
  certificateAction B oneLC all_defined_LC

def certificateLA_RE (B : Nat) (useLA : Bool) : WeightedTNFCertificate B (tableWith (pumpAction useLA)) 6 :=
  certificateAction B (pumpAction useLA) (all_defined_LA_RE useLA)

#print axioms path_to_action
#print axioms certificateRA
#print axioms certificateOneBD
#print axioms certificateLC
#print axioms certificateLA_RE
#print axioms path_to_variant
#print axioms certificateVariant

#print axioms path_to_table
#print axioms certificate
end BB6.Agent47R1Certificate
