import ResetChain
import T0D0ZeroPhaseArithmetic

namespace Agent7D0

open CascadeResetInverse

/-- The arithmetic parentlessness theorem is definitionally the exact
    ResetParent relation certified by the complete source-C inverse grammar. -/
theorem d0_entry_no_source_parent
    (K a r p B D E : Nat)
    (hK : 266 ≤ K)
    (hK18 : K % 18 = 2)
    (ha18 : a % 18 = 2)
    (hra : r+a=K+1)
    (hp : p=2^K)
    (hB : B=(2*K+7)*2^(r+3))
    (hB24 : 24*p ≤ B)
    (hB28 : B ≤ 28*p)
    (hD : 3*D+16*p=B+2*K+1)
    (hE : E+D=8*p+K) :
    ¬ ∃h, CascadeResetInverse.ResetParent h E := by
  simpa [CascadeResetInverse.ResetParent, ResetParentFormula] using
    d0_entry_no_parent K a r p B D E hK hK18 ha18 hra hp hB hB24 hB28 hD hE

/-- Infinite explicit family of first-entry reset heights excluded from the
    blank-root trajectory by the exact source root_reset_chain_iff. -/
theorem d0_family_not_root_reachable (n : Nat) (hn : 1≤n) :
    ∃ K E, K=d0Level n ∧ 266≤K ∧ K%18=2 ∧
      4*2^K≤E+K+4 ∧ E+K+5<8*2^K ∧
      (∃ r B, r%2=1 ∧ B=(2*K+7)*2^(r+3) ∧
        16*2^K+4*K+20≤B ∧ B≤28*2^K+4*K+8 ∧
        3*E+B=40*2^K+K-1) ∧
      ¬ CascadeSource.ReachC (2,0) (E,0) := by
  obtain ⟨K,E,hKexact,hK,hK18,hEgt2,hFirstLo,hFirstHi,hTail,hNo⟩ :=
    explicit_family_no_parent n hn
  have hNoParent : ¬ ∃ h, CascadeResetInverse.ResetParent h E := by
    simpa [CascadeResetInverse.ResetParent, ResetParentFormula] using hNo
  have hNoChain : ¬ CascadeResetInverse.ResetChain 2 E := by
    intro hc
    cases hc with
    | root => omega
    | append hchain hp => exact hNoParent ⟨_,hp⟩
  have hNoReach : ¬ CascadeSource.ReachC (2,0) (E,0) := by
    intro hr
    have hc := (CascadeResetInverse.root_reset_chain_iff E).mp hr
    exact hNoChain hc
  exact ⟨K,E,hKexact,hK,hK18,hFirstLo,hFirstHi,hTail,hNoReach⟩

/-- The excluded first-entry levels are unbounded, so this is genuinely an
    infinite family rather than a finite list of checked examples. -/
theorem d0_family_unbounded_source (M : Nat) :
    ∃ K E, M<K ∧ K%18=2 ∧
      4*2^K≤E+K+4 ∧ E+K+5<8*2^K ∧
      (∃ r B, r%2=1 ∧ B=(2*K+7)*2^(r+3) ∧
        16*2^K+4*K+20≤B ∧ B≤28*2^K+4*K+8 ∧
        3*E+B=40*2^K+K-1) ∧
      ¬ CascadeSource.ReachC (2,0) (E,0) := by
  let n := M+1
  have hn : 1≤n := by omega
  obtain ⟨K,E,hKexact,hK,hK18,hFirstLo,hFirstHi,hTail,hNoReach⟩ :=
    d0_family_not_root_reachable n hn
  refine ⟨K,E,?_,hK18,hFirstLo,hFirstHi,hTail,hNoReach⟩
  rw [hKexact]
  dsimp [d0Level,n]
  have hlinear : 18*(M+1)+1≤2^(18*(M+1)) :=
    linear_le_pow2 (18*(M+1))
  omega

end Agent7D0
