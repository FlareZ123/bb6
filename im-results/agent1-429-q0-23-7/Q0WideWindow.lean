import Q0LongWindow
import Q0WideRank

namespace BB429Q0Macro.HalfStep
open BB429Q0Macro
set_option maxHeartbeats 8000000

/-- Every large q0 candidate forces a two-sided window of radius
    floor(4^k/(128*(k+1))) near a power-of-two rank. -/
theorem q0_wide_cross (u : Nat) (hu : 1000000≤u)
    (h : Path (8*u+5) (24*u+22) (6*u+4)) :
    ∃ a k b, (a=1 ∨ a=2) ∧ 12≤k ∧ b<9 ∧ CrossWindow a b k (wideRadius k) := by
  obtain ⟨w,P,Y,hw,htrace⟩ := RankBarrier.trace_of_path h
  obtain ⟨t,hl,hh⟩ := scale_exists (2*(24*u+22)) (by omega)
  have ht : 12≤t := by
    by_cases he : t<12
    · have hpow := Nat.pow_le_pow_right (n:=4) (by decide) (show t+1≤12 by omega)
      have hval : 4^12=16777216 := by decide
      omega
    · omega
  have hR := RankBarrier.trace_rank htrace
  have hP : P≤16^(t+1) := by
    have hpow := Nat.pow_mul 4 2 (t+1)
    have hpow' : 16^(t+1)=4^(t+1)*4^(t+1) := by
      rw [←hpow,show 2*(t+1)=(t+1)+(t+1) by omega,Nat.pow_add]
    have hge : 2≤4^(t+1) := by
      have := Nat.pow_le_pow_right (n:=4) (by decide) (show 1≤t+1 by omega)
      simp at this; omega
    have hbig := Nat.mul_le_mul_left (4^(t+1)) hge
    rw [hpow']
    omega
  have grow : ∀ j : Nat, 6*j*(t+1)+14≤2*(24*u+22) →
      2*(2*(24*u+22))+2*j≤2*P+14 := by
    intro j hj
    have hmul : 6*j*(t+1)=6*(j*(t+1)) := by rw [Nat.mul_assoc]
    have hj' : j*(t+1)≤w.length := by rw [hw]; omega
    have hg := RankBarrier.extra_growth (k:=t+1) (j:=j) (by omega) htrace
      (by omega) (by omega) hP hj'
    omega
  obtain ⟨a,k,ha,hk,h₁,h₂⟩ := wide_rank_cover t _ (2*P) ht hl hh grow
  obtain ⟨b,hb,hcross⟩ := trace_window (expand_trace htrace) (by omega) (by omega)
    (by simp [valid,bit]) h₁ h₂
  exact ⟨a,k,b,ha,hk,hb,hcross⟩

theorem q0_of_no_wide_cross {Reach : Nat→Nat→Prop} (src : Source Reach)
    (hbar : ∀ a k b, (a=1 ∨ a=2) → 12≤k → b<9 → ¬ CrossWindow a b k (wideRadius k))
    {u n x y : Nat} (hu : 1000000≤u) (hn : n=23+32*u)
    (hx : x+24*u+19=13*2^n) (hy : y+13=2*x) : ¬ Reach x y := by
  intro hr
  obtain ⟨a,k,b,ha,hk,hb,hc⟩ := q0_wide_cross u hu (q0_path src u n x y hn hx hy hr)
  exact hbar a k b ha hk hb hc

#print axioms q0_wide_cross
#print axioms q0_of_no_wide_cross
end BB429Q0Macro.HalfStep
