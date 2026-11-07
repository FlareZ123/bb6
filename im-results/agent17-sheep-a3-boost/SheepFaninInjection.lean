import SheepFaninParameters
namespace SheepFaninInjection
open SheepBoostSourceModel

def IndexedGeneric (a h v y : Nat) : Prop :=
  ∃ q : Nat, v%2=1 ∧ 5≤v ∧ q%2=1 ∧
    GenericF a v=1+2^h*q ∧ y=1+3^h*q

/-- Any finite family of distinct hidden lengths, each supplied with a
legal generic predecessor, provides an injection of that entire index
family into genuine original-source EvenEdge predecessors. -/
theorem finite_length_injection (n a y : Nat) (ha : 1≤a)
    (h : Fin n → Nat) (hinj : Function.Injective h)
    (hex : ∀ i : Fin n, ∃ v : Nat, IndexedGeneric a (h i) v y) :
    ∃ f : Fin n → Nat, Function.Injective f ∧
      ∀ i, SheepEven.EvenEdge (2^a*f i) y := by
  classical
  let f : Fin n → Nat := fun i => Classical.choose (hex i)
  have hf (i : Fin n) : IndexedGeneric a (h i) (f i) y :=
    Classical.choose_spec (hex i)
  refine ⟨f,?_,?_⟩
  · intro i j heq
    obtain ⟨qi,hiodd,himin,hqiodd,hFi,hy_i⟩ := hf i
    obtain ⟨qj,hjodd,hjmin,hqjodd,hFj,hy_j⟩ := hf j
    have hsrc : 2^a*f i=2^a*f j := by rw [heq]
    have hlen : h i = h j :=
      (SheepFaninParameters.index_determined_by_source
        hiodd hjodd hqiodd hqjodd hsrc hFi hFj).2
    exact hinj hlen
  · intro i
    obtain ⟨q,hvodd,hvmin,hqodd,hF,hy⟩ := hf i
    exact SheepFaninOriginal.published_edge_to_source
      ⟨ha,hvodd,hvmin,h i,q,hqodd,hF,hy⟩

#print axioms finite_length_injection
end SheepFaninInjection
