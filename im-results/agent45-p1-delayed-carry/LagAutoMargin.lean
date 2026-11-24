import LagGroup
import LagBound
namespace BB6.Agent45.DelayedCarry

theorem resMin_odd_pos (s B : Nat) (hs : 1≤s) (hB : B%2=1) : 1≤resMin s B := by
  have hd : 2∣(2:Nat)^s := by simpa using Nat.pow_dvd_pow 2 hs
  have hpar : ((7*B)%2^s)%2=1 := by
    rw [Nat.mod_mod_of_dvd _ hd,Nat.mul_mod,hB]
  have hlt : (7*B)%2^s<2^s := Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold resMin
  exact Nat.le_min.mpr ⟨by omega,by omega⟩

/-- Before cost 2n minus a small logarithmic margin, no per-state margin
certificate is needed. Extinction alone certifies every odd-cone coordinate. -/
theorem auto_late_margin (n K s j : Nat) (hj : 1≤j) (hjs : j≤s)
    (hgap : (n+K+2)*marginSize n K*2^s<6*2^n) : LateMargin n K j := by
  intro B a htr
  have hB := (trace_bounds n _ B a htr).2.2.1
  have hR := resMin_odd_pos j B hj hB
  have hL := Nat.mul_le_mul_left ((n+K+2)*marginSize n K) (Nat.pow_le_pow_right (show 0<2 by decide) hjs)
  have hR' := Nat.mul_le_mul_left (6*2^n) hR
  simp only [Nat.mul_one] at hR'
  omega

theorem auto_cert (n K s : Nat) (ps : List Prefix)
    (hcover : Covered n s ps) (hgap : (n+K+2)*marginSize n K*2^s<6*2^n) : Cert n K s ps :=
  ⟨hcover,fun j hj hjs => auto_late_margin n K s j hj hjs hgap⟩

theorem auto_group_cert (n K s : Nat) (gs : List Group) (hcover : GroupCovered n s gs)
    (hgap : (n+K+2)*marginSize n K*2^s<6*2^n) : GroupCert n K s gs :=
  ⟨hcover,fun j hj hjs => auto_late_margin n K s j hj hjs hgap⟩

#print axioms auto_late_margin
end BB6.Agent45.DelayedCarry
