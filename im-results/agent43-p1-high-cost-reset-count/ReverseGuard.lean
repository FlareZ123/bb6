import LagBoundary

namespace BB6.Agent43P1Reverse
open BB6.Agent43LagExact
open BB6.P1CarryExact (Micro LegalGap micro_mass)
open BB6.Agent43LagBoundary

/-- Exact deterministic predecessor test for a guarded unit-cost history.
    At equality the one predecessor is the only possible guarded predecessor;
    the recursion accepts it only at the initial split. -/
def backCheck (n : Nat) : Nat → Nat → Nat → Bool
  | 0, v, w => decide (v=1 ∧ w=BB6.P1CarryExact.total n-n-2)
  | m+1, v, w =>
    if v<w then
      decide (0<m ∧ 2≤v ∧ v+4≤w) &&
        backCheck n m (2*v) (w-v+1)
    else
      decide (2≤v ∧ 5≤w) &&
        backCheck n m (v-w+1) (2*w)

theorem guarded_right_pos {n m v w : Nat} (h : GuardedMicro n m v w) : 0<v := by
  cases h <;> omega

theorem guarded_left_ge_five {n m v w : Nat} (hn : 14≤n)
    (h : GuardedMicro n m v w) : 5≤w := by
  induction h with
  | root =>
    have hbig := BB6.P1CarryExact.pow2_ge_1100_mul n hn
    unfold BB6.P1CarryExact.total
    omega
  | one m v w u z h hs hu hv hw ih => omega
  | zero m v w u z h hm hu hv hw ih =>
    have hmass := micro_mass n m v w hn (guarded_micro h)
    change v+w+n+m+1=BB6.P1CarryExact.total n at hmass
    omega

theorem guarded_back {n m v w : Nat} (hn : 14≤n)
    (h : GuardedMicro n m v w) : backCheck n m v w=true := by
  induction h with
  | root => simp [backCheck]
  | one m v w u z h hs hu hv hw ih =>
    have hmass := micro_mass n m v w hn (guarded_micro h)
    change v+w+n+m+1=BB6.P1CarryExact.total n at hmass
    have hp := guarded_right_pos h
    have hle : ¬ u<z := by omega
    have hV : u-z+1=v := by omega
    have hW : 2*z=w := hw.symm
    simp only [backCheck, if_neg hle, hV,hW,ih,Bool.and_true]
    exact decide_eq_true ⟨hu,by omega⟩
  | zero m v w u z h hm hu hv hw ih =>
    have hmass := micro_mass n m v w hn (guarded_micro h)
    change v+w+n+m+1=BB6.P1CarryExact.total n at hmass
    have hlow := guarded_left_ge_five hn h
    have hlt : u<z := by omega
    have hW : z-u+1=w := by omega
    simp only [backCheck, if_pos hlt, ←hv,hW,ih,Bool.and_true]
    exact decide_eq_true ⟨hm,hu,by omega⟩

theorem back_guarded (n m v w : Nat) (hn : 14≤n)
    (h : backCheck n m v w=true) : GuardedMicro n m v w := by
  induction m generalizing v w with
  | zero =>
    have hh : v=1 ∧ w=BB6.P1CarryExact.total n-n-2 :=
      of_decide_eq_true (by simpa only [backCheck] using h)
    rw [hh.1,hh.2]
    exact GuardedMicro.root
  | succ m ih =>
    by_cases hlt : v<w
    · simp only [backCheck, if_pos hlt] at h
      obtain ⟨hc,hr⟩ := Bool.and_eq_true.mp h
      have hc' : 0<m ∧ 2≤v ∧ v+4≤w := of_decide_eq_true hc
      have hp := ih (2*v) (w-v+1) hr
      have hmass := micro_mass n m (2*v) (w-v+1) hn (guarded_micro hp)
      change 2*v+(w-v+1)+n+m+1=BB6.P1CarryExact.total n at hmass
      exact GuardedMicro.zero m (2*v) (w-v+1) v w hp hc'.1 hc'.2.1 rfl (by omega)
    · simp only [backCheck, if_neg hlt] at h
      obtain ⟨hc,hr⟩ := Bool.and_eq_true.mp h
      have hc' : 2≤v ∧ 5≤w := of_decide_eq_true hc
      have hp := ih (v-w+1) (2*w) hr
      have hmass := micro_mass n m (v-w+1) (2*w) hn (guarded_micro hp)
      change (v-w+1)+2*w+n+m+1=BB6.P1CarryExact.total n at hmass
      exact GuardedMicro.one m (v-w+1) (2*w) v w hp (by omega) hc'.1 (by omega) rfl

theorem back_iff_guarded (n m v w : Nat) (hn : 14≤n) :
    backCheck n m v w=true ↔ GuardedMicro n m v w :=
  ⟨back_guarded n m v w hn, guarded_back hn⟩

/-- A genuine complete gap endpoint is decided by the deterministic reverse
    recursion with a single final guard. -/
theorem back_iff_legal (n m v w : Nat) (hn : 14≤n) :
    LegalGap n m v w ↔ backCheck n m v w=true ∧ (m=0 ∨ 6≤w) := by
  rw [legal_iff_guarded hn,back_iff_guarded n m v w hn]

/-- After the first compulsory split the entire diagonal, plus the three
    adjacent points on the zero-predecessor side, is forbidden. -/
theorem forbidden_middle {n m v w : Nat} (hn : 14≤n)
    (hm : 1<m) (h : GuardedMicro n m v w) :
    v>w ∨ v+4≤w := by
  cases h with
  | root => omega
  | one m v w u z h hs hu hv hw =>
    have hmass := micro_mass n m v w hn (guarded_micro h)
    change v+w+n+m+1=BB6.P1CarryExact.total n at hmass
    have hp : 2≤v := by cases h <;> omega
    exact Or.inl (by omega)
  | zero m v w u z h hpos hu hv hw =>
    have hmass := micro_mass n m v w hn (guarded_micro h)
    change v+w+n+m+1=BB6.P1CarryExact.total n at hmass
    have hp := guarded_left_ge_five hn h
    exact Or.inr (by omega)

/-- The exact endpoint checker can be consumed at the authentic critical
    gate without any upper-cost cutoff or margin premise. -/
theorem critical_reset_no_reach_of_back (n : Nat) (hn : 14≤n) (he : n%2=0)
    (h : ∀ m v w, 0<m → 6≤w → Boundary n m v w →
      backCheck n m v w=false) :
    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  intro hr
  obtain ⟨m,B,a,hT,hW,hB⟩ := critical_reset_requires_guarded_boundary n hn he hr
  have hG := guarded_trace_to_micro hn he hT
  have ht := guarded_trace_trace hT
  have hm := (BB6.Agent45.DelayedCarry.trace_bounds n m B a ht).1
  have hc := guarded_back hn hG
  rw [h m _ _ hm hW hB] at hc
  contradiction

#print axioms back_iff_guarded
#print axioms back_iff_legal
#print axioms forbidden_middle
#print axioms critical_reset_no_reach_of_back
end BB6.Agent43P1Reverse
