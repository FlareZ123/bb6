import CapPhaseCost
import CapPhaseSource
namespace CapSieve

/-- Any small-root history below the exceptional-exit cost and above the
    low bands must continue by one of the two regular positive branches. -/
theorem small_root_positive_continues {j s k x : Nat} {w : Int} (hw : 0<w)
    (h : PositiveHistory j w s k x) (hk : 6≤k) (hb : Band k x)
    (hpos : 0<W k x) (hr : Cap.rootOf x≤3)
    (hc : (3^s:Int)*(6*(k:Int)+35)<4*(3^(j-k):Int)*(P k:Int)+6+w) :
    ∃ z, Arc z x ∧ ((PositiveHistory j w (s+1) k z ∧ 0<W k z) ∨
      (PositiveHistory j w (s+1) (k-1) z ∧ 0<W (k-1) z)) := by
  have hsafe : P k+3≤x := by
    by_cases he : x≤P k+2
    · have hh:=positive_boundary_cost_bandsharp hw h he
      omega
    · omega
  have hp:=p_ge_large hk
  have hl:=l_add k
  have hx : 3<x := by have := hb.1; omega
  cases he : Cap.predecessor x with
  | none =>
    have hh : Cap.rootOf x=x := by rw [Cap.rootOf.eq_def,he]
    omega
  | some z =>
    have ha:=arc_iff_pred.mpr he
    refine ⟨z,ha,?_⟩
    rcases (positive_to_negative hk hb hpos ha) with h0|h1|h2|h3
    · exact Or.inl ⟨.same h h0.1,h0.2⟩
    · have hi : k-1+1=k := by omega
      have h' : PositiveHistory j w s (k-1+1) x := by rw [hi]; exact h
      exact Or.inr ⟨.down h' h1.1,h1.2⟩
    · obtain ⟨r,hh,_,heq⟩:=h2.1
      have hp : P k=4*P (k-2) := by
        calc
          P k=P ((k-2)+1+1) := congrArg P (by omega)
          _=4*P (k-2) := by rw [p_succ,p_succ]; omega
      omega
    · omega

#print axioms small_root_positive_continues
end CapSieve
