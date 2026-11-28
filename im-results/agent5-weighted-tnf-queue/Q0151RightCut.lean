import Q0151Category
import Q0151FiniteModel

set_option maxHeartbeats 0
namespace BB6.Agent5Q0151RightCut
open BB6.Agent5Q0151Category
open BB6.Agent5Q0151FiniteModel

/-!
Soundness fragments for the q0-151 right-tape run decomposition.
An arbitrarily long first run may be replaced by its finite category.
If a hypothetical next run and remainder mask lead to a given suffix
mask, the right 'cut' enumerator retains that hypothetical successor.
These lemmas do not assert a nonhalting source invariant by themselves.
-/

theorem dnext_cat (g : Int) (n : Nat) :
    dnext g (cat n) = dnext g n := by
  simp only [dnext,cat_mod]

theorem pre_cat (n t : Nat) :
    pre (cat n) t = pre n t := by
  unfold pre
  rw [dnext_cat 0 n,dnext_cat 1 n]

theorem pre_lt_four (n t : Nat) : pre n t < 4 := by
  cases h0 : maskAccept t (dnext 0 n) <;>
    cases h1 : maskAccept t (dnext 1 n) <;>
    simp [pre,h0,h1]

theorem front_complete (c suffix t : Nat)
    (hc : c ∈ firstVariants) (hs : suffix ∈ suffixVariants)
    (hp : pre c suffix = t) :
    (c, ⟨c,suffix⟩) ∈ front t := by
  unfold front
  apply List.mem_flatMap.mpr
  refine ⟨c,hc,?_⟩
  apply List.mem_map.mpr
  refine ⟨suffix,?_,rfl⟩
  exact List.mem_filter.mpr ⟨hs,hp⟩

theorem cut_complete (first c suffix : Nat)
    (hf : first ≠ 0)
    (hc : c ∈ firstVariants) (hs : suffix ∈ suffixVariants) :
    (first, ⟨c,suffix⟩) ∈ cut ⟨first,pre c suffix⟩ := by
  have ht : pre c suffix ≠ 4 := Nat.ne_of_lt (pre_lt_four c suffix)
  simp only [cut,if_neg hf,if_neg ht]
  apply List.mem_map.mpr
  refine ⟨(c,⟨c,suffix⟩),front_complete c suffix
    (pre c suffix) hc hs rfl,?_⟩
  rfl

theorem cut_empty : (0,emptyRight) ∈ cut emptyRight := by decide

#print axioms dnext_cat
#print axioms pre_cat
#print axioms pre_lt_four
#print axioms front_complete
#print axioms cut_complete
end BB6.Agent5Q0151RightCut
