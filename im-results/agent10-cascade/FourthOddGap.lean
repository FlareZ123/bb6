import FourthExactTwo
set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace CascadeAgent10OddGap
open CascadeResetInverse CascadeUniformFatal CascadeAgent10Four CascadeAgent10FourthBranch CascadeAgent10ExactlyTwo

/-- The would-be t=2 odd first-reset inverse lies in a prohibited dyadic
    band gap for all fourth ancestors, regardless of residue class. -/
theorem fourth_no_odd_ttwo (n:Nat) (hn:10≤n) :
    ¬∃ k d:Nat,
      (6*2^k+1 ≤ 4*d ∧ 4*d ≤ 8*2^k-1) ∧
      2*fourthPred n+5=27*d := by
  rintro ⟨k,d,⟨hl,hu⟩,heq⟩
  have hgrowth := band_growth n hn
  have hh : fourthPred n+31*n+49=4*2^n := by
    dsimp [fourthPred]
    omega
  have hqlo : 2^n < 4*d := by omega
  have hqhi : 2*(4*d) < 3*2^n := by omega
  by_cases hk:k+3≤n
  · have hp : 2^(k+3)≤2^n := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hk
    have hp8 : 2^(k+3)=8*2^k:=by rw [Nat.pow_add];omega
    rw [hp8] at hp
    omega
  · have hk2 : n-2≤k := by omega
    have hp : 2^(n-2)≤2^k := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hk2
    have hp4 : 2^n=4*2^(n-2) := by
      have he : 2^n=2^((n-2)+2):=congrArg (fun m:Nat=>2^m) (by omega)
      rw [Nat.pow_add] at he
      omega
    omega

#print axioms fourth_no_odd_ttwo
end CascadeAgent10OddGap
