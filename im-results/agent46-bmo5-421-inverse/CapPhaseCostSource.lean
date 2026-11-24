import CapPhaseCost
import CapPhaseSource
namespace CapSieve

/-- If the exceptional-return cost has not yet been paid, an actual
    small-root predecessor must be one of the two regular positive branches.
    Skip and special exits are ruled out by their sharper return costs. -/
theorem small_root_positive_continues {j s k x : Nat} {w : Int} (hw : 0<w)
    (h : PositiveHistory j w s k x) (hk : 6≤k) (hb : Band k x)
    (hpos : 0<W k x) (hr : Cap.rootOf x≤3)
    (hc : (3^s:Int)*(6*(k:Int)+27)<4*(3^(j-k):Int)*(P k:Int)+6+w) :
    ∃ z, Arc z x ∧ ((PositiveHistory j w (s+1) k z ∧ 0<W k z) ∨
      (PositiveHistory j w (s+1) (k-1) z ∧ 0<W (k-1) z)) := by
  have hp:=p_ge_large hk
  have hl:=l_add k
  have hx : 3<x := by
    have hx':=hb.1
    omega
  cases he:Cap.predecessor x with
  | none =>
    have hh : Cap.rootOf x=x := by rw [Cap.rootOf.eq_def,he]
    omega
  | some z =>
    have ha:=arc_iff_pred.mpr he
    refine ⟨z,ha,?_⟩
    rcases positive_to_negative hk hb hpos ha with h0|h1|h2|h3
    · exact Or.inl ⟨.same h h0.1,h0.2⟩
    · have hi : k-1+1=k := by omega
      have h' : PositiveHistory j w s (k-1+1) x := by rw [hi]; exact h
      exact Or.inr ⟨.down h' h1.1,h1.2⟩
    · have hh:=positive_skip_parent_cost hw (by omega) h h2.1
      have hD : 0<(3^s:Int) := Int.pow_pos (by decide)
      have hbase : 6*(k:Int)-9<6*(k:Int)+27 := by omega
      have hstrict : (3^s:Int)*(6*(k:Int)-9)<(3^s:Int)*(6*(k:Int)+27) :=
        Int.mul_lt_mul_of_pos_left hbase hD
      omega
    · have hxP : x=P k := h3.1
      subst x
      have hh:=positive_special_return_cost hw h
      omega
#print axioms small_root_positive_continues
end CapSieve
