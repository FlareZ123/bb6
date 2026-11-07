import SheepFaninInjection
import SheepFaninAllK
namespace SheepFaninEvenA3N
open SheepBoostSourceModel SheepFaninInjection SheepFaninAllK

/-- Explicit hidden-length witness for any allowed valuation-three
source at even k, retaining its index for distinctness arguments. -/
theorem even_a3_indexed (s t : Nat) (hbound : 16*t+10 ≤ 2*s+1) :
    ∃ v, IndexedGeneric 3 (16*t+10) v (2^(2*3^(2*s))) := by
  have hk : 1 ≤ 2*s := by omega
  obtain ⟨q,hqmin,hpow,_⟩ := power_quotient (2*s) (16*t+10) hk hbound
  have hpow' : 3^(16*t+10)*q+1=2^(2*9^s) := by
    simpa only [pow_index_even] using hpow
  obtain ⟨v,hvmin,hvodd,heq⟩ := SheepA3Boost.parent_even s t q hpow' hqmin
  have heq' : (2^(3+1)+1)*v+(2*3-3)=2^((16*t+10)+1)*q := by
    simpa [show 16*t+10+1=16*t+11 by omega] using heq
  have hj : 0 < 2*3^(2*s) := by
    have hp : 0 < (3:Nat)^(2*s) := Nat.pow_pos (by decide)
    omega
  have hodd : q%2=1 := odd_quotient_of_power (2*3^(2*s))
      (16*t+10) q hj hpow
  have hF := generic_return_identity 3 v (16*t+10) q
    (by decide) hvodd heq'
  refine ⟨v,q,hvodd,hvmin,hodd,hF,?_⟩
  omega

/-- Explicit n pairwise different genuine original-source predecessors
of the same power target, where the linear upper index bound enforces
that all n hidden lengths are admissible. -/
theorem even_a3_n_distinct (s n : Nat) (hbound : 10+16*n ≤ 2*s+17) :
    ∃ f : Fin n → Nat, Function.Injective f ∧
      ∀ i, SheepEven.EvenEdge (8*f i) (2^(2*3^(2*s))) := by
  let h : Fin n → Nat := fun i => 16*i.val+10
  have hinj : Function.Injective h := by
    intro i j he
    apply Fin.ext
    dsimp [h] at he
    omega
  have hex : ∀ i : Fin n,
      ∃ v, IndexedGeneric 3 (h i) v (2^(2*3^(2*s))) := by
    intro i
    have hle : 16*i.val+10 ≤ 2*s+1 := by
      have hi := i.isLt
      omega
    exact even_a3_indexed s i.val hle
  obtain ⟨f,hf,he⟩ := finite_length_injection n 3
    (2^(2*3^(2*s))) (by decide) h hinj hex
  exact ⟨f,hf,by intro i; simpa only [show (2:Nat)^3=8 by decide] using he i⟩

#print axioms even_a3_indexed
#print axioms even_a3_n_distinct
end SheepFaninEvenA3N
