import Lean.Elab.Tactic.Omega

namespace BB6.Agent11HighDepthUnique

private theorem residues_distinct_when_lt (j m r s : Nat)
    (hlt : r < s)
    (hr : (j+9*m+14)%2^(r+4)=3*2^(r+2))
    (hs : (j+9*m+14)%2^(s+4)=3*2^(s+2)) : False := by
  let D := j+9*m+14
  have hdivr : (2:Nat)^(r+3) ∣ (2:Nat)^(r+4) :=
    Nat.pow_dvd_pow 2 (by omega)
  have hdivs : (2:Nat)^(r+3) ∣ (2:Nat)^(s+4) :=
    Nat.pow_dvd_pow 2 (by omega)
  have hdivmid : (2:Nat)^(r+3) ∣ (2:Nat)^(s+2) :=
    Nat.pow_dvd_pow 2 (by omega)
  have hdivprod : (2:Nat)^(r+3) ∣ 3*2^(s+2) := by
    rcases hdivmid with ⟨v,hv⟩
    refine ⟨3*v,?_⟩
    rw [hv]
    ac_rfl
  have hp : 0<(2:Nat)^(r+2) := Nat.pow_pos (by decide)
  have he : (2:Nat)^(r+3) = 2*2^(r+2) := by
    rw [show r+3=(r+2)+1 by omega, Nat.pow_succ]
    omega
  have hR : D%2^(r+3)=2^(r+2) := by
    calc
      D%2^(r+3) = (D%2^(r+4))%2^(r+3) :=
        (Nat.mod_mod_of_dvd D hdivr).symm
      _ = (3*2^(r+2))%2^(r+3) := by
        simpa only [D] using congrArg (fun z : Nat => z%2^(r+3)) hr
      _ = 2^(r+2) := by
        rw [he]
        let t := (2:Nat)^(r+2)
        have ht : 3*t = 2*t+t := by omega
        change (3*t)%(2*t)=t
        have htpos : 0 < t := hp
        rw [ht]
        have hmod : (2*t+t)%(2*t) = t%(2*t) := by
          rw [Nat.add_mod]
          simp
        rw [hmod]
        exact Nat.mod_eq_of_lt (by omega)
  have hS : D%2^(r+3)=0 := by
    calc
      D%2^(r+3) = (D%2^(s+4))%2^(r+3) :=
        (Nat.mod_mod_of_dvd D hdivs).symm
      _ = (3*2^(s+2))%2^(r+3) := by
        simpa only [D] using congrArg (fun z : Nat => z%2^(r+3)) hs
      _ = 0 := Nat.mod_eq_zero_of_dvd hdivprod
  omega

/-- Distinct inverse depths have disjoint stopping-residue tests.
    Consequently, at most one depth can eliminate any fixed (j,m). -/
theorem high_gate_unique_depth (j m r s : Nat)
    (hr : (j+9*m+14)%2^(r+4)=3*2^(r+2))
    (hs : (j+9*m+14)%2^(s+4)=3*2^(s+2)) : r=s := by
  by_cases hlt : r<s
  · exact False.elim (residues_distinct_when_lt j m r s hlt hr hs)
  · by_cases hgt : s<r
    · exact False.elim (residues_distinct_when_lt j m s r hgt hs hr)
    · omega

#print axioms high_gate_unique_depth
end BB6.Agent11HighDepthUnique
