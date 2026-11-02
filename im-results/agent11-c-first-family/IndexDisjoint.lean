import IndexWitness
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11

private theorem powered_oddpart_no_lt
    (r q t u : Nat)
    (h : 2^(2*r)*(4*t+1)=2^(2*q)*(4*u+1)) : ¬ r<q := by
  intro hlt
  have hsplit : 2*q=2*r+2*(q-r) := by omega
  have heq : 4*t+1=2^(2*(q-r))*(4*u+1) := by
    have eq2 : 2^(2*r)*(4*t+1) =
        2^(2*r)*(2^(2*(q-r))*(4*u+1)) := by
      calc
        2^(2*r)*(4*t+1) = 2^(2*q)*(4*u+1) := h
        _ = 2^(2*r)*(2^(2*(q-r))*(4*u+1)) := by
            rw [hsplit, Nat.pow_add]
            ac_rfl
    exact Nat.mul_left_cancel (Nat.pow_pos (by decide)) eq2
  have h4 : 4 ∣ 2^(2*(q-r)) := by
    have he : 2*(q-r)=2+(2*(q-r)-2) := by omega
    rw [he, Nat.pow_add]
    change 4 ∣ 4*2^(2*(q-r)-2)
    exact ⟨2^(2*(q-r)-2),rfl⟩
  obtain ⟨v,hv⟩ := h4
  rw [hv] at heq
  have : 4 ∣ 4*t+1 := by
    rw [heq]
    exact ⟨v*(4*u+1),by ac_rfl⟩
  omega

/-- Exactly one 4-adic depth can certify any particular first-family
    index. The infinite depth families are pairwise disjoint. -/
theorem index_depth_unique (r q s t u : Nat)
    (hr : 63*s+11=2^(2*r)*(4*t+1))
    (hq : 63*s+11=2^(2*q)*(4*u+1)) : r=q := by
  have heq : 2^(2*r)*(4*t+1)=2^(2*q)*(4*u+1) :=
    hr.symm.trans hq
  have hle : ¬ r<q := powered_oddpart_no_lt r q t u heq
  have hge : ¬ q<r := powered_oddpart_no_lt q r u t heq.symm
  omega

#print axioms index_depth_unique
end BB6.Agent11
