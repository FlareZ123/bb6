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

theorem r1_never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨z,hz⟩ := all_defined n
  have H := zrun_sound table m hm n start z hz
  rw [initial_embed] at H
  change (run m n blank).isSome = true
  rw [H]
  rfl

#print axioms r1_never
end BB6Coverage.Agent47R1Sweep

namespace BB6.Agent47R1Certificate
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath BB6.Agent50TNFPilot
open BB6Coverage.Agent47R1Sweep

def schedule : List PathEntry :=
  [(1,(1,false),⟨true,false,2⟩),
   (2,(2,true),⟨false,false,3⟩),
   (3,(3,false),⟨true,false,2⟩),
   (4,(2,false),⟨false,false,4⟩),
   (5,(4,false),⟨false,true,0⟩),
   (7,(1,true),⟨false,true,1⟩),
   (10,(4,true),⟨true,false,5⟩),
   (11,(5,false),⟨true,false,0⟩),
   (49,(0,true),⟨false,false,2⟩),
   (52,(5,true),⟨false,false,1⟩)]

abbrev endpoint : PartialMachine := (pathEnd root 2 schedule).1

def tableEq (a b : PartialMachine) : Bool :=
  (List.finRange 6).all fun q => [false,true].all fun s => decide (a (q,s) = b (q,s))

theorem tableEq_sound (a b : PartialMachine) (h : tableEq a b = true) : a = b := by
  funext x
  rcases x with ⟨q,bv⟩
  have hq := List.all_eq_true.mp h q (List.mem_finRange q)
  have hb : bv ∈ [false,true] := by cases bv <;> simp
  exact of_decide_eq_true (List.all_eq_true.mp hq bv hb)

theorem endpoint_eq : endpoint = table := tableEq_sound _ _ (by decide)

theorem path_to_table : FirstHolePath table 6 := by
  have H := pathOK_sound root 2 schedule FirstHolePath.root (show pathOK root 2 schedule = true by decide)
  have hc : (pathEnd root 2 schedule).2 = 6 := by decide
  rw [hc] at H
  change FirstHolePath endpoint 6 at H
  rw [endpoint_eq] at H
  exact H

def certificate (B : Nat) : WeightedTNFCertificate B table 6 :=
  .nonhalt (by decide) (support6 _) (by
    rw [← endpoint_eq]
    exact pathEnd_nohalt root 2 schedule firstOneCylinder_no_assigned_halt) r1_never

#print axioms path_to_table
#print axioms certificate
end BB6.Agent47R1Certificate
