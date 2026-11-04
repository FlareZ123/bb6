import SecondGateFanInjective
import BounceOriginal
import FastSectionDef
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Research

open BB6.Agent46

/-- A genuine second-stopping-family target has a whole parameterized
    family of exact incoming source section edges. These inputs are
    synthetically constructed; reachability from the blank tape is open. -/
theorem second_gate_incoming_edge (s t : Nat) :
  secNext (FanArithmetic.p s t, FanArithmetic.q s t) =
    some (FanArithmetic.x s t, FanArithmetic.y s t) := by
  open FanArithmetic in
    have hbound := FanArithmetic.bounds s t
    have hA := FanArithmetic.a_ge_b s t
    have hB : FanArithmetic.b s t=3*FanArithmetic.m s t+4 := rfl
    have hp : FanArithmetic.p s t+3=4*FanArithmetic.a s t := by
      unfold FanArithmetic.p
      omega
    have h0 : FanArithmetic.p s t≠0 := by omega
    have h1 : FanArithmetic.p s t≠1 := by omega
    have hk0 : FanArithmetic.q s t≠0 := by omega
    have hregion : ¬(2*FanArithmetic.q s t≤FanArithmetic.p s t) := by omega
    have heven : (FanArithmetic.p s t-1)%2=0 := by omega
    have hy : 5≤FanArithmetic.y s t := by
      have hD := FanArithmetic.d_ge s t
      have heq := FanArithmetic.y_eq s t
      omega
    have hbounce :
      (bounce (FanArithmetic.p s t-1)
        (2*FanArithmetic.q s t-FanArithmetic.p s t+3)).2 =
        some (FanArithmetic.x s t,FanArithmetic.y s t) :=
      (bounce_even_image
        (FanArithmetic.p s t-1)
        (2*FanArithmetic.q s t-FanArithmetic.p s t+3)
        (FanArithmetic.x s t) (FanArithmetic.y s t) heven).mpr
        (Or.inr ⟨2*s+1,hy,FanArithmetic.source_sum s t,FanArithmetic.source_cost s t⟩)
    simpa [secNext, exactSection, h0, h1, hk0, hregion] using hbounce

theorem second_gate_fan (n : Nat) :
    ∃ f : Fin n → Nat × Nat,
      Function.Injective f ∧
      ∀ i, secNext (f i)=some (FanArithmetic.secondX n,FanArithmetic.secondY n) := by
  refine ⟨FanArithmetic.source n,FanArithmetic.source_injective n,?_⟩
  intro i
  have ht:=second_gate_incoming_edge i.val (n-i.val-1)
  have hxy:=FanArithmetic.source_target n i
  change secNext (FanArithmetic.p i.val (n-i.val-1),
    FanArithmetic.q i.val (n-i.val-1)) =
    some (FanArithmetic.secondX n,FanArithmetic.secondY n)
  rw [←hxy.1,←hxy.2]
  exact ht

/-- For every target predecessor count n there is a mathematically genuine
    second stopping-family parameter gate with at least n distinct incoming
    accelerated-section edges. None of these edges is asserted blank reachable. -/
theorem second_halting_family_unbounded_indegree (n : Nat) :
    ∃ j m k : Nat, ∃ f : Fin n → Nat × Nat,
      k+j+3*m+5=2^(2*m+2)*(j+3) ∧
      Function.Injective f ∧
      (∀ i, secNext (f i)=some (2*j+3,k)) := by
  obtain ⟨f,hf,hi⟩ := second_gate_fan n
  refine ⟨3*n+1,n,FanArithmetic.secondY n,f,
    FanArithmetic.second_halt_parameter n,hf,?_⟩
  intro i
  have heq : 2*(3*n+1)+3=FanArithmetic.secondX n := by
    unfold FanArithmetic.secondX
    omega
  rw [heq]
  exact hi i

#print axioms second_gate_incoming_edge
#print axioms second_gate_fan
#print axioms second_halting_family_unbounded_indegree
end BB6.Agent11Research
