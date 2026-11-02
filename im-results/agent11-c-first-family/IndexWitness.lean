import Lean.Elab.Tactic.Omega

namespace BB6.Agent11

/-- Exact 2-adic index witness at every unbounded inverse depth.
    The three seeds propagate via s ↦ 64*s+11 and r ↦ r+3. -/
theorem index_witness (r : Nat) :
    ∃ s t : Nat, 63*s+11 = 2^(2*r)*(4*t+1) := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
      rcases r with _ | _ | _ | r
      · exact ⟨2,34,by decide⟩
      · exact ⟨7,28,by decide⟩
      · exact ⟨59,58,by decide⟩
      · obtain ⟨s,t,hs⟩ := ih r (by omega)
        refine ⟨64*s+11,t,?_⟩
        have hr : r+1+1+1=r+3 := by omega
        rw [hr]
        have hpow : 2^(2*(r+3))=64*2^(2*r) := by
          have hh : 2*(r+3)=2*r+6 := by omega
          rw [hh, Nat.pow_add]
          rw [show (2:Nat)^6=64 by decide]
          omega
        calc
          63*(64*s+11)+11 = 64*(63*s+11) := by omega
          _ = 64*(2^(2*r)*(4*t+1)) := by rw [hs]
          _ = (64*2^(2*r))*(4*t+1) := by ac_rfl
          _ = 2^(2*(r+3))*(4*t+1) := by rw [hpow]

/-- For every depth the admissible parameter set is unbounded in s.
    This exact witness is constructed by shifting any seed solution by
    a multiple of 4*2^(2r), with the complementary t shift by 63. -/
theorem index_witness_unbounded (r lower : Nat) :
    ∃ s t : Nat, lower ≤ s ∧ 63*s+11=2^(2*r)*(4*t+1) := by
  obtain ⟨s,t,hs⟩ := index_witness r
  let P : Nat := 2^(2*r)
  have hP : 0<P := Nat.pow_pos (by decide)
  refine ⟨s+4*P*lower,t+63*lower,?_,?_⟩
  · have hp1 : 1 ≤ 4*P := by omega
    have hp2 : lower ≤ (4*P)*lower :=
      Nat.le_mul_of_pos_left lower (by omega : 0<4*P)
    omega
  · change 63*(s+4*P*lower)+11=P*(4*(t+63*lower)+1)
    have hh : 63*s+11=P*(4*t+1) := hs
    calc
      63*(s+4*P*lower)+11 =
          (63*s+11)+P*(4*(63*lower)) := by
            simp only [Nat.mul_add]
            ac_rfl
      _ = P*(4*t+1)+P*(4*(63*lower)) := by rw [hh]
      _ = P*(4*(t+63*lower)+1) := by
            simp only [Nat.mul_add]
            ac_rfl

#print axioms index_witness
#print axioms index_witness_unbounded
end BB6.Agent11
