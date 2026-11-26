import Q0LongWindow
import OddResetWideRank

namespace BB429Q0Macro.HalfStep
open BB429Q0Macro
set_option maxHeartbeats 8000000

theorem path_wide_cross_defect14 {m p y : Nat} (h : Path m p y) (hy : 0<y) (hc : 3*y<p)
    (hmin : 4^11 ≤ 2*p) (hlength : 3*m≤p) (hdef : p≤3*m+14) :
    ∃ a k b, (a=1∨a=2) ∧ 11≤k ∧ b<9 ∧ CrossWindow a b k (wideRadius k) := by
  obtain ⟨w,P,Y,hw,htrace⟩ := RankBarrier.trace_of_path h
  obtain ⟨t,hl,hh⟩ := scale_exists (2*p) (by omega)
  have ht : 11≤t := by
    by_cases he : t<11
    · have hpow := Nat.pow_le_pow_right (n:=4) (by decide) (show t+1≤11 by omega)
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
  have grow : ∀ j : Nat, 6*j*(t+1)+28≤2*p → 2*(2*p)+2*j≤2*P+28 := by
    intro j hj
    have hmul : 6*j*(t+1)=6*(j*(t+1)) := by rw [Nat.mul_assoc]
    have hj' : j*(t+1)≤w.length := by rw [hw]; omega
    have hg := RankBarrier.extra_growth (k:=t+1) (j:=j) (by omega) htrace hy hc hP hj'
    omega
  obtain ⟨a,k,ha,hk,h₁,h₂⟩ := wide_rank_cover_defect28 t _ (2*P) ht hl hh grow
  obtain ⟨b,hb,hcross⟩ := trace_window (expand_trace htrace) (by omega) (by omega) (by simp [valid,bit]) h₁ h₂
  exact ⟨a,k,b,ha,hk,hb,hcross⟩

theorem oddFF_wide_cross (t : Nat) (ht : 43750≤t)
    (h : Path (13+16*t) (53+48*t) (3+3*t)) :
    ∃ a k b, (a=1∨a=2) ∧ 11≤k ∧ b<9 ∧ CrossWindow a b k (wideRadius k) := by
  apply path_wide_cross_defect14 h <;> omega

theorem oddFE_wide_cross (t : Nat) (ht : 43750≤t)
    (h : Path (8+16*t) (36+48*t) (11+15*t)) :
    ∃ a k b, (a=1∨a=2) ∧ 11≤k ∧ b<9 ∧ CrossWindow a b k (wideRadius k) := by
  apply path_wide_cross_defect14 h <;> omega

#print axioms path_wide_cross_defect14
#print axioms oddFF_wide_cross
#print axioms oddFE_wide_cross
end BB429Q0Macro.HalfStep
