import ModScreen
import BudgetCore
namespace BB6.Agent28ModScreen
open BB6.Agent28CarryBudget BB6.Agent28BitCarry
def budgetIndices (p : Nat × Nat) : List Nat :=
  (certIndices p).filter (fun n => budgetOK n p.2)
def budgetTargets : List Nat := targetIndices.filter (fun n => n != 34)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem budget_coverage_ok : bits (certs.flatMap budgetIndices) = bits budgetTargets := by decide +kernel

theorem budget_witness_of_coverage (n : Nat)
    (hlo : 14≤n) (hhi : n≤10000) (he : n%2=0)
    (hs : survivor n=false) (h34 : n≠34)
    (hvalid : ∀ p∈certs, p.1%2=0 ∧ listRun p.1 1 [((p.1+2)/2)] p.2=[]) :
    ∃ r k t, r%2=0 ∧ k+1≤n ∧ n=r+2^(k+1)*t ∧
      listRun r 1 [((r+2)/2)] k=[] ∧ budgetOK n k=true := by
  have ht : n∈targetIndices := by
    simp [targetIndices,hlo,he,hs]; omega
  have hbt : n∈budgetTargets := by simp [budgetTargets,ht,h34]
  have hbit := (bit_mem budgetTargets n).2 hbt
  rw [← budget_coverage_ok] at hbit
  obtain ⟨p,hp,hm⟩ := List.mem_flatMap.mp ((bit_mem _ n).1 hbit)
  have hv := hvalid p hp
  simp only [budgetIndices,List.mem_filter] at hm
  obtain ⟨r,k⟩ := p
  obtain ⟨hcover,hbudget⟩ := hm
  simp only [certIndices,List.mem_filter,Bool.and_eq_true,decide_eq_true_eq,
    Prod.fst,Prod.snd] at hcover
  by_cases hK : k+1≤14
  · rw [if_pos hK] at hcover
    obtain ⟨t,_,h⟩ := List.mem_map.mp hcover.1
    exact ⟨r,k,t,hv.1,hcover.2.1.1.2.2,h.symm,hv.2,hbudget⟩
  · rw [if_neg hK] at hcover
    have h : n=r := List.mem_singleton.mp hcover.1
    exact ⟨r,k,0,hv.1,hcover.2.1.1.2.2,by simp [h],hv.2,hbudget⟩

theorem certificate_with_budget (n : Nat)
    (hlo : 14≤n) (hhi : n≤10000) (he : n%2=0)
    (hs : survivor n=false) (h34 : n≠34) :
    ∃ r k t, r%2=0 ∧ k+1≤n ∧ n=r+2^(k+1)*t ∧
      listRun r 1 [((r+2)/2)] k=[] ∧ budgetOK n k=true :=
  budget_witness_of_coverage n hlo hhi he hs h34
    (fun p hp => checkCert_sound p (List.all_eq_true.mp certs_ok p hp))

#print axioms budget_coverage_ok
#print axioms certificate_with_budget
end BB6.Agent28ModScreen
