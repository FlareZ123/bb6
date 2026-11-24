import ZeroTwoRootCover
import Lean.Elab.Tactic.Omega

namespace BB429.ZeroTwoDiagonalCover
open ZeroTwoRootCover
set_option maxHeartbeats 10000000

private theorem le_pow_two (n : Nat) : n ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    have h : 0 < 2^n := Nat.pow_pos (by decide)
    omega

/-- The valuation of a+3 on the exact diagonal upper feeder is the
    valuation of m-2, with its odd part determined modulo eight. -/
theorem diagonal_factor (m J N a z k r : Nat)
    (hk : 4≤k) (hr : r%2=1)
    (hm : m=2+2^k*r) (hJ : J=4*m+2) (hN : N=8*2^J+J-11)
    (hz : z+48*2^J+3*J=12*2^(N+2)+36)
    (ha : z=4*a+18) :
    ∃ c, 9≤c ∧ c%2=1 ∧ (c+3*r)%8=0 ∧ a=2^k*c-3 := by
  let t := 2^k
  let x := 2^(J-k)
  let y := 2^(N-k)
  have ht : 16≤t := Nat.pow_le_pow_right (n:=2) (by decide) hk
  have hkt : k≤t := le_pow_two k
  have htr : t≤t*r := Nat.le_mul_of_pos_right t (by omega)
  have hrt : r≤t*r := Nat.le_mul_of_pos_left r (by omega)
  change m=2+t*r at hm
  have hkJ : k+3≤J := by omega
  have hJbig : 10≤J := by omega
  have hpowJ : 4≤2^J := Nat.pow_le_pow_right (n:=2) (by decide) (show 2≤J by omega)
  have hJN : J+1≤N := by omega
  have hx : 0<x := Nat.pow_pos (by decide)
  have hrx : r≤x := by
    have h : r≤J-k := by omega
    exact Nat.le_trans h (le_pow_two (J-k))
  have hy : 2*x≤y := by
    have hh : 2^(J-k+1)≤2^(N-k) := Nat.pow_le_pow_right (n:=2) (by decide) (by omega)
    rw [Nat.pow_succ] at hh
    dsimp [x,y]; omega
  let c := 12*y-12*x-3*r
  have hc : 9≤c := by dsimp [c]; omega
  have hX : 2^J=t*x := by
    dsimp [t,x]
    rw [← Nat.pow_add,show k+(J-k)=J by omega]
  have hY : 2^N=t*y := by
    dsimp [t,y]
    rw [← Nat.pow_add,show k+(N-k)=N by omega]
  have hcx : c+12*x+3*r=12*y := by dsimp [c]; omega
  have hmul := congrArg (fun q : Nat => t*q) hcx
  simp only [Nat.mul_add,Nat.mul_left_comm t 12,Nat.mul_left_comm t 3] at hmul
  have hN2 : 2^(N+2)=4*2^N := by rw [Nat.pow_add,show (2:Nat)^2=4 by decide,Nat.mul_comm]
  rw [hN2,hX,hY] at hz
  have ha' : a=t*c-3 := by omega
  have hx8 : x%8=0 := by
    dsimp [x]
    rw [show J-k=3+(J-k-3) by omega,Nat.pow_add,show (2:Nat)^3=8 by decide]
    omega
  have hy8 : y%8=0 := by
    dsimp [y]
    rw [show N-k=3+(N-k-3) by omega,Nat.pow_add,show (2:Nat)^3=8 by decide]
    omega
  exact ⟨c,hc,by omega,by omega,ha'⟩

/-- Every rooted upper diagonal feeder with m-2=2^k*r, k>=4, r odd,
    has an actual S exit or one of the four valuation endpoint classes.
    This is a necessary cover, not a positive reachability claim. -/
theorem diagonal_root_cover (m J N a z k r : Nat)
    (hk : 4≤k) (hr : r%2=1)
    (hm : m=2+2^k*r) (hJ : J=4*m+2) (hN : N=8*2^J+J-11)
    (hz : z+48*2^J+3*J=12*2^(N+2)+36)
    (ha : z=4*a+18) (hroot : Rooted (a,2*a+2)) :
    (∃ c, 9≤c ∧ c%2=1 ∧ (c+3*r)%8=0 ∧ a=2^k*c-3 ∧ SideExit k c) ∨
    (k%16=0 ∧ r%8=5) ∨ (k%16=4 ∧ r%8=3) ∨
    (k%16=8 ∧ r%8=1) ∨ (k%16=12 ∧ r%8=7) := by
  obtain ⟨c,hc,ho,hc8,hac⟩ := diagonal_factor m J N a z k r hk hr hm hJ hN hz ha
  have hupper : Rooted (upper k c) := by
    unfold upper
    rw [← hac]
    exact hroot
  rcases upper_root_cover k c hk hc ho hupper with hside|hclasses
  · exact Or.inl ⟨c,hc,ho,hc8,hac,hside⟩
  · right
    omega

#print axioms diagonal_factor
#print axioms diagonal_root_cover
end BB429.ZeroTwoDiagonalCover
