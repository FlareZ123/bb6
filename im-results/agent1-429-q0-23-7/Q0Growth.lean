import Q0DoubleBarrier

namespace BB429Q0Macro.RankBarrier
open BB429Q0Macro
set_option maxHeartbeats 4000000

theorem minimal_cost_all_zero (w : List Digit) (h : L w=3*w.length) : D w=0 ∧ E w=0 := by
  have hl (v : List Digit) : 3*v.length≤L v := by
    induction v with
    | nil => simp [L]
    | cons d v ih => cases d <;> simp [L,cost] at * <;> omega
  induction w with
  | nil => simp [D,E]
  | cons d w ih =>
    have hw := hl w
    cases d <;> simp [L,cost] at h
    · obtain ⟨hD,hE⟩ := ih (by omega)
      simp [D,E,digit,offset,hD,hE]
    all_goals omega

/-- A strict trace of k macros below rank 16^k cannot have minimal cost. -/
theorem block_extra {w p y P Y : _} (h : Trace w p y P Y) (hy : 0<y) (hp : 3*y<p)
    (hP : P≤16^w.length) : p+3*w.length+1≤P := by
  have hr := trace_rank h
  by_cases hbad : p+3*w.length+1≤P
  · exact hbad
  obtain ⟨hl,hform⟩ := trace_formula h
  have hL : L w=3*w.length := by omega
  obtain ⟨hD,hE⟩ := minimal_cost_all_zero w hL
  have hY := (trace_strict h hy hp).1
  simp [hD,hE,M] at hform
  have hpos : (1:Int)≤Y := by omega
  have hm : 0≤(16:Int)^w.length := Int.le_of_lt (Int.pow_pos (by decide))
  have hmul := Int.mul_le_mul_of_nonneg_left hpos hm
  have hP' : (P:Int)≤(16:Int)^w.length := by exact_mod_cast hP
  omega

/-- Every full k-block contributes at least one extra unit of rank. -/
theorem extra_growth {k j : Nat} (hk : 0<k) {w p y P Y : _} (h : Trace w p y P Y)
    (hy : 0<y) (hp : 3*y<p) (hP : P≤16^k) (hj : j*k≤w.length) :
    p+3*w.length+j≤P := by
  induction j generalizing w p y with
  | zero => have hh := trace_rank h; omega
  | succ j ih =>
    obtain ⟨Q,F,h₁,h₂⟩ := trace_split h k
    have hjk : k≤w.length := by rw [Nat.succ_mul] at hj; omega
    have hl : (w.take k).length=k := by simp [Nat.min_eq_left hjk]
    have hl₂ : (w.drop k).length=w.length-k := by simp
    have hr := trace_rank h₂
    have hQ : Q≤16^k := by omega
    have hq := block_extra h₁ hy hp (by simpa [hl] using hQ)
    have hf := trace_strict h₁ hy hp
    have hj' : j*k≤(w.drop k).length := by rw [hl₂]; simp [Nat.succ_mul] at hj; omega
    have he := ih h₂ hf.1 hf.2 hj'
    omega

#print axioms block_extra
#print axioms extra_growth
end BB429Q0Macro.RankBarrier
