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
      simp only [Bool.and_eq_true] at h
      obtain ⟨hc,hr⟩ := h
      have hc' : 0<m ∧ 2≤v ∧ v+4≤w := of_decide_eq_true hc
      have hp := ih (2*v) (w-v+1) hr
      have hmass := micro_mass n m (2*v) (w-v+1) hn (guarded_micro hp)
      change 2*v+(w-v+1)+n+m+1=BB6.P1CarryExact.total n at hmass
      exact GuardedMicro.zero m (2*v) (w-v+1) v w hp hc'.1 hc'.2.1 rfl (by omega)
    · simp only [backCheck, if_neg hlt] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨hc,hr⟩ := h
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

/-- Exact run jump in the zero predecessor branch.  The last guard
    dominates all the earlier ones. -/
theorem zero_jump (n m v w k : Nat) (hm : k<m) (hv : 2≤v)
    (hf : 2^k*v+5≤v+w+k) :
    backCheck n m v w =
      backCheck n (m-k) (2^k*v) (v+w+k-2^k*v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    let p := 2^k*v
    have hp : 2≤p := by
      have hpow : 1≤2^k := Nat.one_le_pow _ _ (by decide)
      have hmul := Nat.mul_le_mul_right v hpow
      dsimp [p]
      exact Nat.le_trans hv (by simpa using hmul)
    have hpow : 2^(k+1)*v=2*p := by
      dsimp [p]
      rw [Nat.pow_succ]
      ac_rfl
    have hf0 : p+5≤v+w+k := by rw [hpow] at hf; omega
    have hprev := ih (by omega) (by simpa [p] using hf0)
    calc
      backCheck n m v w = backCheck n (m-k) p (v+w+k-p) := by
        simpa only [p] using hprev
      _ = _ := by
        let q := v+w+k-p
        have hguard : p+4≤q := by dsimp [q]; rw [hpow] at hf; omega
        have hlt : p<q := by omega
        have hidx : m-k=(m-(k+1))+1 := by omega
        change backCheck n (m-k) p q = _
        rw [hidx,backCheck,if_pos hlt]
        have hdec : decide (0<m-(k+1) ∧ 2≤p ∧ p+4≤q)=true :=
          decide_eq_true ⟨by omega,hp,hguard⟩
        rw [hdec,Bool.true_and,hpow]
        have hq : q-p+1=v+w+(k+1)-2*p := by dsimp [q]; omega
        rw [hq]

/-- Exact run jump in the selected predecessor branch, including the
    possibility that the last jump reaches the original cost-zero root. -/
theorem one_jump (n m v w k : Nat) (hm : k≤m) (hw : 5≤w)
    (hf : 2^k*w+1≤v+w+k) :
    backCheck n m v w =
      backCheck n (m-k) (v+w+k-2^k*w) (2^k*w) := by
  induction k with
  | zero => simp
  | succ k ih =>
    let p := 2^k*w
    have hp : 5≤p := by
      have hpow : 1≤2^k := Nat.one_le_pow _ _ (by decide)
      have hmul := Nat.mul_le_mul_right w hpow
      dsimp [p]
      exact Nat.le_trans hw (by simpa using hmul)
    have hpow : 2^(k+1)*w=2*p := by
      dsimp [p]
      rw [Nat.pow_succ]
      ac_rfl
    have hf0 : p+1≤v+w+k := by rw [hpow] at hf; omega
    have hprev := ih (by omega) (by simpa [p] using hf0)
    calc
      backCheck n m v w = backCheck n (m-k) (v+w+k-p) p := by
        simpa only [p] using hprev
      _ = _ := by
        let q := v+w+k-p
        have hguard : p≤q := by dsimp [q]; rw [hpow] at hf; omega
        have hlt : ¬q<p := by omega
        have hidx : m-k=(m-(k+1))+1 := by omega
        change backCheck n (m-k) q p = _
        rw [hidx,backCheck,if_neg hlt]
        have hdec : decide (2≤q ∧ 5≤p)=true :=
          decide_eq_true ⟨by omega,hp⟩
        rw [hdec,Bool.true_and,hpow]
        have hq : q-p+1=v+w+(k+1)-2*p := by dsimp [q]; omega
        rw [hq]

/-- The power feeder is a single point on each fixed-mass diagonal,
    with its dyadic index determined by a strict dyadic band. -/
theorem power_boundary_coords (S v w j : Nat) (hm : v+w=S)
    (hv : 5≤v) (hw : 6≤w) (ho : v%2=1) (h : w+v/2=7*2^j) :
    7*2^j+3≤S ∧ S+5≤14*2^j ∧
      v=2*S-14*2^j-1 ∧ w=14*2^j+1-S := by
  omega

theorem power_boundary_index_unique (S j k : Nat)
    (hj : 7*2^j+3≤S ∧ S+5≤14*2^j)
    (hk : 7*2^k+3≤S ∧ S+5≤14*2^k) : j=k := by
  by_cases h : j<k
  · have hp := Nat.pow_le_pow_right (show 0<2 by decide) (show j+1≤k by omega)
    rw [Nat.pow_succ] at hp
    omega
  · by_cases h' : k<j
    · have hp := Nat.pow_le_pow_right (show 0<2 by decide) (show k+1≤j by omega)
      rw [Nat.pow_succ] at hp
      omega
    · omega

#print axioms zero_jump
#print axioms one_jump
#print axioms power_boundary_coords
#print axioms power_boundary_index_unique


/-- A complete fixed-index exclusion needs at most seven endpoint tests
per positive cost. No delayed-prefix cutoff or numerical margin is assumed. -/
theorem critical_reset_no_reach_of_families (n : Nat) (hn : 14≤n) (he : n%2=0)
    (h : ∀ m, 0<m → m+n+9≤BB6.P1CarryExact.total n →
      let S := BB6.P1CarryExact.total n-(n+m+1)
      (∀ w, 6≤w → w≤10 → backCheck n m (S-w) w=false) ∧
      ((n+m)%2=0 → backCheck n m 2 (S-2)=false) ∧
      (∀ j, j<n → 7*2^j+3≤S → S+5≤14*2^j →
        backCheck n m (2*S-14*2^j-1) (14*2^j+1-S)=false)) :
    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  intro hr
  obtain ⟨m,B,a,hT,hW,hB⟩ := critical_reset_requires_guarded_boundary n hn he hr
  have hG := guarded_trace_to_micro hn he hT
  have ht := guarded_trace_trace hT
  have hm := (BB6.Agent45.DelayedCarry.trace_bounds n m B a ht).1
  have hc := guarded_back hn hG
  let v := rightAt n m B a
  let w := leftAt n m B a
  change 6≤w at hW
  change Boundary n m v w at hB
  change backCheck n m v w=true at hc
  change GuardedMicro n m v w at hG
  have hv : 2≤v := by cases hG <;> omega
  have hmass := micro_mass n m v w hn (guarded_micro hG)
  change v+w+n+m+1=BB6.P1CarryExact.total n at hmass
  let S := BB6.P1CarryExact.total n-(n+m+1)
  have hS : v+w=S := by dsimp [S]; omega
  have hcases := h m hm (by omega)
  change (∀ w, 6≤w → w≤10 → backCheck n m (S-w) w=false) ∧
    ((n+m)%2=0 → backCheck n m 2 (S-2)=false) ∧
    (∀ j, j<n → 7*2^j+3≤S → S+5≤14*2^j →
      backCheck n m (2*S-14*2^j-1) (14*2^j+1-S)=false) at hcases
  rcases hB with hsmall | ⟨h2,hpar⟩ | ⟨h5,hodd,j,hj,hpow⟩
  · have hv' : v=S-w := by omega
    rw [hv',hcases.1 w hW hsmall] at hc
    contradiction
  · have hw' : w=S-2 := by omega
    rw [h2,hw',hcases.2.1 hpar] at hc
    contradiction
  · obtain ⟨hlo,hhi,hv',hw'⟩ := power_boundary_coords S v w j hS h5 hW hodd hpow
    rw [hv',hw',hcases.2.2 j hj hlo hhi] at hc
    contradiction

#print axioms critical_reset_no_reach_of_families

end BB6.Agent43P1Reverse
