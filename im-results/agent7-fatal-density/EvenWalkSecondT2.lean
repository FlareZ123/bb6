import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace GapSecondTTwo
private theorem gap_odd (n q:Nat) (hl:2^n<q)
    (hu:2*q+2<3*2^n) :
    ∀k, ¬(6*2^k+1 ≤ q ∧ q ≤ 8*2^k-1) := by
  intro k ⟨hlo,hhi⟩
  by_cases hk:k+3≤n
  · have hp : 2^(k+3)≤2^n := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hk
    have he : 2^(k+3)=8*2^k := by rw [Nat.pow_add];omega
    rw [he] at hp
    omega
  · have hnk : n≤k+2 := by omega
    have hp : 2^n≤2^(k+2) := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hnk
    have he : 2^(k+2)=4*2^k := by rw [Nat.pow_add];omega
    rw [he] at hp
    omega

/-- All-index exclusion of the SECOND-TIER t=2 odd return to a true
    narrow w gate, where the source numerator is exactly 27*d. -/
theorem narrow_w_ttwo_impossible (n w k d:Nat) (hn:4≤n)
 (hl:2^n<w) (hu:8*w+32<9*2^n)
 (hd:2*w+5=27*d)
 (hb:6*2^k+1≤4*d ∧4*d≤8*2^k-1): False := by
 have hscale:2^n=4*2^(n-2):=by
   have he:n=(n-2)+2:=by omega
   rw [he,Nat.pow_add]
   simp [Nat.mul_comm]
 have hlo:2^(n-2)<4*d:=by
   rw[hscale] at hl
   omega
 have hhi:2*(4*d)+2<3*2^(n-2):=by
   rw[hscale] at hu
   omega
 exact (gap_odd (n-2) (4*d) hlo hhi) k hb

#print axioms narrow_w_ttwo_impossible
end GapSecondTTwo
