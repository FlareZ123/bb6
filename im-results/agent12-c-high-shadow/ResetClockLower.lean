import CountedOrdinary
import RankClock
import Lean

namespace BB6.Agent12ResetLower
open BB6CLine BB6.Agent47ThinCounted BB6.Agent12CountedOrdinary
set_option maxHeartbeats 0

def major (s : State) : Prop := s.2.2=0 ∨ s.1=0 ∧ 4≤s.2.2
def boundary (s : State) : Prop := major s ∨ s.2.2=2

def drain (s : State) : State :=
  let h := min s.1 (s.2.2-3)
  (s.1-h,s.2.1+h,s.2.2-h)

def finish : State → State
  | (a,k,1) => (a,k+1,0)
  | (a,k,3) => (a,k+3,0)
  | s => s

def settle (s : State) := finish (drain s)
def jump (s : State) := (nextC s).map settle

theorem drain_path (s : State) : ∃ n w, Path n w s (drain s) := by
  rcases s with ⟨a,k,c⟩
  by_cases hc : c≤3
  · have he : drain (a,k,c)=(a,k,c) := by simp [drain,show c-3=0 by omega]
    rw [he]; exact ⟨0,0,Path.nil _⟩
  · let h := min a (c-3)
    have ha : h≤a := Nat.min_le_left _ _
    have he : h≤c-3 := Nat.min_le_right _ _
    have p := sweep_counted h (a-h) k (c-h) (by omega)
    rw [show a-h+h=a by omega,show c-h+h=c by omega] at p
    exact ⟨_,_,p⟩

theorem finish_path (s : State) : ∃ n w, Path n w s (finish s) := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · exact ⟨0,0,Path.nil _⟩
  · exact ⟨1,2,Path.cons (by rfl : nextC (a,k,1)=some (a,k+1,0)) (Path.nil _)⟩
  · exact ⟨0,0,Path.nil _⟩
  · exact ⟨2,14,finish3 a k⟩
  · exact ⟨0,0,Path.nil _⟩

theorem settle_path (s : State) : ∃ n w, Path n w s (settle s) := by
  obtain ⟨n,w,p⟩ := drain_path s
  obtain ⟨m,v,q⟩ := finish_path (drain s)
  exact ⟨n+m,w+v,p.append q⟩

theorem settle_boundary (s : State) : boundary (settle s) := by
  rcases s with ⟨a,k,c⟩
  by_cases hh : a≤c-3
  · simp only [settle,drain,Nat.min_eq_left hh,Nat.sub_self]
    generalize c-a=d
    rcases d with _|_|_|_|d <;> simp [finish,boundary,major] <;> omega
  · have hca : c-3≤a := by omega
    simp only [settle,drain,Nat.min_eq_right hca]
    have hc : c-(c-3)≤3 := by omega
    generalize c-(c-3)=d at *
    rcases d with _|_|_|_|d <;> simp [finish,boundary,major] <;> omega

theorem drain_rank (s : State) : rankC (drain s)=rankC s := by
  rcases s with ⟨a,k,c⟩
  have h1 := Nat.min_le_left a (c-3)
  have h2 := Nat.min_le_right a (c-3)
  simp only [drain,rankC]
  omega

theorem finish_rank (s : State) : rankC s≤rankC (finish s) ∧ rankC (finish s)≤rankC s+3 := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d <;> simp [finish,rankC] <;> omega

theorem settle_rank (s : State) : rankC s≤rankC (settle s) ∧ rankC (settle s)≤rankC s+3 := by
  have h := finish_rank (drain s)
  rw [drain_rank] at h
  exact h

theorem major_edge_rank {s t : State} (hs : major s) (h : nextC s=some t) :
    rankC s<rankC t ∧ rankC t≤rankC s+5 := by
  rcases s with ⟨a,k,c⟩
  rcases hs with hc|⟨ha,hc⟩
  · change c=0 at hc; subst c
    rcases a with _|_|a
    · simp only [nextC,Option.some.injEq] at h; subst t; simp [rankC]; omega
    · rcases k with _|k <;> simp only [nextC,Option.some.injEq] at h <;> subst t <;> simp [rankC] <;> omega
    · simp only [nextC,Option.some.injEq] at h; subst t; simp [rankC]; omega
  · change a=0 at ha; change 4≤c at hc; subst a
    obtain ⟨d,rfl⟩ : ∃ d,c=d+4 := ⟨c-4,by omega⟩
    by_cases he:k%2=0 <;> simp only [nextC,he,ite_true,ite_false,Option.some.injEq] at h <;> subst t <;> simp [rankC] <;> omega

theorem jump_exists (s : State) (hs : major s) : ∃ t, jump s=some t := by
  rcases s with ⟨a,k,c⟩
  rcases hs with hc|⟨ha,hc⟩
  · change c=0 at hc; subst c
    rcases a with _|_|a
    · exact ⟨_,rfl⟩
    · rcases k with _|k <;> exact ⟨_,rfl⟩
    · exact ⟨_,rfl⟩
  · change a=0 at ha; change 4≤c at hc; subst a
    obtain ⟨d,rfl⟩ : ∃ d,c=d+4 := ⟨c-4,by omega⟩
    by_cases he:k%2=0
    · simp [jump,nextC,he]
    · simp [jump,nextC,he]

theorem jump_spec {s t : State} (hs : major s) (hj : jump s=some t) :
    ∃ u n w, nextC s=some u ∧ Path n w u t ∧ boundary t ∧ rankC s<rankC t ∧ rankC t≤rankC s+8 := by
  unfold jump at hj
  cases he : nextC s with
  | none => simp [he] at hj
  | some u =>
    simp [he] at hj
    subst t
    obtain ⟨n,w,p⟩ := settle_path u
    have hr := major_edge_rank hs he
    have hsettle := settle_rank u
    exact ⟨u,n,w,rfl,p,settle_boundary u,by omega,by omega⟩

/-- Small right counter relative to the rank forces exact doubling growth
    at the next reset, even when the reset is a bounce rather than a section. -/
theorem cheap_growth {s t : State} (hs : major s) (hj : jump s=some t)
    (hsmall : 4*s.2.1+9≤rankC s) :
    major t ∧ 2*s.2.1+2≤t.2.1 := by
  rcases s with ⟨a,k,c⟩
  rcases hs with hc|⟨ha,hc⟩
  · change c=0 at hc; subst c
    simp only [rankC] at hsmall
    obtain ⟨A,rfl⟩ : ∃ A,a=A+2 := ⟨a-2,by omega⟩
    rcases k with _|k
    · simp [jump,nextC,settle,drain,finish] at hj
      subst t; simp [major]
    · have hmin : min A (2*(k+1)+1-3)=2*k := by rw [Nat.min_eq_right (by omega)]; omega
      have hc3 : 2*(k+1)+1-2*k=3 := by omega
      simp only [jump,nextC,Option.map_some,Option.some.injEq,settle,drain,hmin,hc3,finish] at hj
      subst t; simp [major]; omega
  · change a=0 at ha; change 4≤c at hc; subst a
    simp only [rankC] at hsmall
    obtain ⟨d,rfl⟩ : ∃ d,c=d+4 := ⟨c-4,by omega⟩
    by_cases he:k%2=0
    · have hmin : min (4*(k/2)+2) (d+1-3)=4*(k/2)+2 := Nat.min_eq_left (by omega)
      have hD : 4≤d+1-(4*(k/2)+2) := by omega
      simp only [jump,nextC,he,ite_true,Option.map_some,Option.some.injEq,settle,drain,hmin,Nat.sub_self] at hj
      obtain ⟨D,hD'⟩ : ∃ D,d+1-(4*(k/2)+2)=D+4 := ⟨d+1-(4*(k/2)+2)-4,by omega⟩
      rw [hD'] at hj
      simp only [finish] at hj
      subst t; simp [major]; omega
    · have hmin : min (4*(k/2)+5) (d+4-3)=4*(k/2)+5 := Nat.min_eq_left (by omega)
      have hD : 4≤d+4-(4*(k/2)+5) := by omega
      simp only [jump,nextC,he,ite_false,Option.map_some,Option.some.injEq,settle,drain,hmin,Nat.sub_self] at hj
      obtain ⟨D,hD'⟩ : ∃ D,d+4-(4*(k/2)+5)=D+4 := ⟨d+4-(4*(k/2)+5)-4,by omega⟩
      rw [hD'] at hj
      simp only [finish] at hj
      subst t; simp [major]; omega

/-- A nonnegative quadratic stored-clock potential. Minor c=1,3 transitions
    preserve it; a sweep increment raises it by at most the literal weight. -/
def stored (s : State) : Nat := 2*(s.2.1+min s.2.2 3-3)^2
def charge (s : State) : Nat := stored s-8

theorem stored_le (s : State) : stored s≤2*s.2.1^2 := by
  have hm:=Nat.min_le_right s.2.2 3
  have hh : s.2.1+min s.2.2 3-3≤s.2.1 := by omega
  exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hh 2)

theorem major_edge_store {s t : State} (hs : major s) (h : nextC s=some t) :
    stored t≤8 ∧ stored t≤weight s := by
  have hb:=stored_le t
  rcases s with ⟨a,k,c⟩
  rcases hs with hc|⟨ha,hc⟩
  · change c=0 at hc; subst c
    rcases a with _|_|a
    · simp only [nextC,Option.some.injEq] at h; subst t; simp [weight] at *; omega
    · rcases k with _|k <;> simp only [nextC,Option.some.injEq] at h <;> subst t <;> simp [weight] at * <;> omega
    · simp only [nextC,Option.some.injEq] at h; subst t; simp [weight] at *; omega
  · change a=0 at ha; change 4≤c at hc; subst a
    obtain ⟨d,rfl⟩ : ∃ d,c=d+4 := ⟨c-4,by omega⟩
    by_cases he:k%2=0 <;> simp only [nextC,he,ite_true,ite_false,Option.some.injEq] at h <;> subst t <;> simp [weight,he] at * <;> omega

theorem major_charge {s t : State} (hs : major s) (h : nextC s=some t) :
    stored t+charge s≤stored s+weight s := by
  have hb:=major_edge_store hs h
  unfold charge
  omega

theorem edge_store {s t : State} (h : nextC s=some t) : stored t≤stored s+weight s := by
  by_cases hs : major s
  · have hh:=major_charge hs h; omega
  · rcases s with ⟨a,k,c⟩
    rcases c with _|_|_|_|d
    · exact False.elim (hs (Or.inl rfl))
    · simp only [nextC,Option.some.injEq] at h; subst t
      change 2*(k+1-3)^2≤2*(k+1-3)^2+2
      omega
    · simp [nextC] at h
    · simp only [nextC,Option.some.injEq] at h; subst t
      change 2*(k+2+1-3)^2≤2*(k+3-3)^2+12
      have he : k+2+1-3=k+3-3 := by omega
      rw [he]; omega
    · rcases a with _|a
      · exact False.elim (hs (Or.inr ⟨rfl,by simp⟩))
      · simp only [nextC,Option.some.injEq] at h; subst t
        simp only [stored,weight,Nat.min_eq_right (show 3≤d+3 by omega),Nat.min_eq_right (show 3≤d+4 by omega),Nat.add_sub_cancel]
        grind

theorem path_store {n w : Nat} {s t : State} (p : Path n w s t) : stored t≤stored s+w := by
  induction p with
  | nil => simp
  | cons h p ih => have hh:=edge_store h; omega

theorem edge_rank_mono {s t : State} (h : nextC s=some t) : rankC s≤rankC t := by
  by_cases hs : major s
  · have hh:=major_edge_rank hs h; omega
  · rcases s with ⟨a,k,c⟩
    rcases c with _|_|_|_|d
    · exact False.elim (hs (Or.inl rfl))
    · simp only [nextC,Option.some.injEq] at h; subst t; simp [rankC]; omega
    · simp [nextC] at h
    · simp only [nextC,Option.some.injEq] at h; subst t; simp [rankC]; omega
    · rcases a with _|a
      · exact False.elim (hs (Or.inr ⟨rfl,by simp⟩))
      · simp only [nextC,Option.some.injEq] at h; subst t; simp [rankC]; omega

theorem path_rank_mono {n w : Nat} {s t : State} (p : Path n w s t) : rankC s≤rankC t := by
  induction p with
  | nil => simp
  | cons h p ih => exact Nat.le_trans (edge_rank_mono h) ih

/-- Every expensive reset in a rank band loses at least the band-scale
    quadratic amount of stored potential. -/
theorem expensive_charge (X : Nat) (s : State) (hX : 64≤X) (hr : X≤rankC s)
    (he : rankC s<4*s.2.1+9) : (X/8)^2≤charge s := by
  have hh : X/8≤s.2.1+min s.2.2 3-3 := by omega
  have hsq := Nat.pow_le_pow_left hh 2
  have h8 : 8≤X/8 := by omega
  have hp := Nat.pow_le_pow_left h8 2
  unfold charge stored
  omega

def depth (s : State) := (s.2.1+1).log2

theorem depth_lt (s : State) (L : Nat) (hL : rankC s<2^L) (hr : 1≤rankC s) : depth s<L := by
  have hk : s.2.1+1≤rankC s := by unfold rankC at *; omega
  exact (Nat.log2_lt (by omega)).mpr (by omega)

theorem cheap_depth {s t : State} (hs : major s) (hj : jump s=some t)
    (hc : 4*s.2.1+9≤rankC s) : depth s+1≤depth t := by
  have hg:=(cheap_growth hs hj hc).2
  have hpow := Nat.log2_self_le (n:=s.2.1+1) (by omega)
  unfold depth
  apply (Nat.le_log2 (by omega)).mpr
  rw [Nat.pow_succ]
  omega

def scale (X : Nat) := (X/8)^2
def factor (L : Nat) := 8*(L+1)

/-- One reset jump pays for rank growth or increases its binary depth.
    The high-reset quadratic charge is independent of the bounce depth. -/
theorem jump_budget (X L : Nat) {s u t : State} {n w : Nat}
    (hs : major s) (he : nextC s=some u) (p : Path n w u t)
    (hj : jump s=some t) (hX : 64≤X) (hr : X≤rankC s)
    (hL : rankC s<2^L) :
    scale X*rankC t+8*scale X*depth s+factor L*stored t≤
      scale X*rankC s+8*scale X*depth t+factor L*(stored s+(weight s+w)) := by
  obtain ⟨_,_,_,_,_,_,_,hgap⟩ := jump_spec hs hj
  have hrank:=Nat.mul_le_mul_left (scale X) hgap
  simp only [Nat.mul_add] at hrank
  rw [Nat.mul_comm (scale X) 8] at hrank
  have hstore:=path_store p
  have hcharge:=major_charge hs he
  by_cases hc : 4*s.2.1+9≤rankC s
  · have hd:=Nat.mul_le_mul_left (8*scale X) (cheap_depth hs hj hc)
    have hb:=Nat.mul_le_mul_left (factor L) (show stored t≤stored s+(weight s+w) by omega)
    simp only [Nat.mul_add,Nat.mul_one] at hd hb ⊢
    omega
  · have hd:=Nat.mul_le_mul_left (8*scale X) (show depth s≤L by have :=depth_lt s L hL (by omega); omega)
    have hc' := expensive_charge X s hX hr (by omega)
    have hb:=Nat.mul_le_mul_left (factor L) (show stored t+scale X≤stored s+(weight s+w) by unfold scale; omega)
    have heq : factor L*scale X=8*scale X*L+8*scale X := by
      unfold factor
      simp only [Nat.mul_add,Nat.mul_one,Nat.add_mul]
      congr 1; ac_rfl
    simp only [Nat.mul_add] at hb ⊢
    rw [heq] at hb
    omega

/-- Every finite successful prefix of a terminal path has an exact
    residual path with the remaining calls and weight. -/
theorem terminal_suffix {n w m v : Nat} {s t u : State} (p : Path n w s t)
    (ht : nextC t=none) (q : Path m v s u) :
    ∃ n' w', n=m+n' ∧ w=v+w' ∧ Path n' w' u t := by
  induction q generalizing n w t with
  | nil => exact ⟨n,w,by simp,by simp,p⟩
  | cons h q ih =>
    cases p with
    | nil => rw [ht] at h; contradiction
    | cons h' p =>
      rw [h] at h'
      have hh:=Option.some.inj h'
      subst_vars
      obtain ⟨n',w',hn,hw,hp⟩ := ih p ht
      exact ⟨n',w',by omega,by omega,hp⟩

theorem stop_of_c2 (s : State) (h : s.2.2=2) : nextC s=none := by
  rcases s with ⟨a,k,c⟩
  change c=2 at h; subst c; rfl

/-- Telescoping reset budgets cover the whole literal terminal suffix.
    There is no assumption that it stays in the ordinary section region. -/
theorem terminal_band_budget (X L n w : Nat) (s t : State)
    (p : Path n w s t) (hs : boundary s) (ht : nextC t=none)
    (hX : 64≤X) (hr : X≤rankC s) (hL : rankC t<2^L) :
    scale X*rankC t+8*scale X*depth s+factor L*stored t≤
      scale X*rankC s+8*scale X*depth t+factor L*(stored s+w) := by
  induction n using Nat.strongRecOn generalizing s w with
  | ind n ih =>
    rcases hs with hm|hstop
    · obtain ⟨z,hz⟩ := jump_exists s hm
      obtain ⟨u,m,v,he,q,hb,hinc,hgap⟩ := jump_spec hm hz
      obtain ⟨n',w',hn,hw,p'⟩ := terminal_suffix p ht (Path.cons he q)
      have h1:=jump_budget X L hm he q hz hX hr (Nat.lt_of_le_of_lt (path_rank_mono p) hL)
      have h2:=ih n' (by omega) w' z p' hb (by omega)
      rw [hw]
      simp only [Nat.mul_add] at h1 h2 ⊢
      omega
    · have he:=stop_of_c2 s hstop
      cases p with
      | nil => simp
      | cons h _ => rw [he] at h; contradiction

/-- A terminal orbit crosses a prescribed rank at a reset boundary, with
    an overshoot of at most seven. No full computation is needed. -/
theorem band_entry (X n w : Nat) (s t : State) (p : Path n w s t)
    (hs : boundary s) (ht : nextC t=none) (hl : rankC s≤X) (hh : X≤rankC t) :
    ∃ z n' w', boundary z ∧ X≤rankC z ∧ rankC z<X+8 ∧ w'≤w ∧ Path n' w' z t := by
  induction n using Nat.strongRecOn generalizing s w with
  | ind n ih =>
    by_cases hnow : X≤rankC s
    · exact ⟨s,n,w,hs,hnow,by omega,by omega,p⟩
    · rcases hs with hm|hstop
      · obtain ⟨z,hz⟩ := jump_exists s hm
        obtain ⟨u,m,v,he,q,hb,hinc,hgap⟩ := jump_spec hm hz
        obtain ⟨n',w',hn,hw,p'⟩ := terminal_suffix p ht (Path.cons he q)
        by_cases hcross : X≤rankC z
        · exact ⟨z,n',w',hb,hcross,by omega,by omega,p'⟩
        · obtain ⟨z',n'',w'',hb',h1,h2,h3,hp'⟩ := ih n' (by omega) w' z p' hb (by omega)
          exact ⟨z',n'',w'',hb',h1,h2,by omega,hp'⟩
      · have he:=stop_of_c2 s hstop
        cases p with
        | nil => omega
        | cons h _ => rw [he] at h; contradiction

/-- Explicit lower clock bound for a halting trajectory from the first
    genuine section. Choose X near half of the terminal rank and L just
    above its binary logarithm. -/
theorem terminal_clock_lower (X L n w : Nat) (t : State)
    (p : Path n w (5,1,0) t) (ht : nextC t=none)
    (hX : 64≤X) (hR : X≤rankC t) (hL : rankC t<2^L) :
    scale X*rankC t≤scale X*(X+8+8*L)+factor L*(w+2*(X+8)^2) := by
  obtain ⟨z,n',w',hb,hr,hgap,hw,p'⟩ := band_entry X n w (5,1,0) t p (Or.inl (Or.inl rfl)) ht (by simp [rankC]; omega) hR
  have hbudget:=terminal_band_budget X L n' w' z t p' hb ht hX hr hL
  have hd:=depth_lt t L hL (by omega)
  have hstore:=stored_le z
  have hk : z.2.1≤X+8 := by unfold rankC at hgap; omega
  have hsquare:=Nat.pow_le_pow_left hk 2
  have h1:=Nat.mul_le_mul_left (scale X) (show rankC z≤X+8 by omega)
  have h2:=Nat.mul_le_mul_left (8*scale X) (show depth t≤L by omega)
  have h3:=Nat.mul_le_mul_left (factor L) (show stored z+w'≤w+2*(X+8)^2 by omega)
  simp only [Nat.mul_add] at hbudget h1 h3 ⊢
  have heq : scale X*(8*L)=8*scale X*L := by ac_rfl
  rw [heq]
  omega

/-- Simultaneous exact-source upper and lower score bounds on the same
    reachable terminal rank. N counts ordinary moves; score is N+1. -/
theorem raw_terminal_clock_bounds (N : Nat) (h : BB6Coverage.HaltsAfter BB6.Agent47CRaw.cMachine N) :
    ∃ t : State, BB6CLine.Reach t ∧ nextC t=none ∧
      6*(N+1)+204≤(rankC t)^3+6*(rankC t)^2 ∧
      ∀ X L : Nat, 64≤X → X≤rankC t → rankC t<2^L →
        scale X*rankC t≤scale X*(X+8+8*L)+factor L*(N+1+2*(X+8)^2) := by
  obtain ⟨n,w,t,p,ht,hN⟩ := (BB6.Agent47CRaw.raw_haltsAfter_iff N).mp h
  obtain ⟨u,hu,hs,hupper⟩ := BB6.Agent12RankClock.raw_halt_rank_bound N h
  obtain ⟨m,v,q⟩ := BB6.Agent47CRaw.reach_path hu
  have he := (p.terminal_unique ht q hs).2.2
  rw [←he] at hupper
  have p0 : Path 1 2 (5,0,1) (5,1,0) := Path.cons (by rfl) (Path.nil _)
  obtain ⟨n',w',hn,hw,p'⟩ := terminal_suffix p ht p0
  refine ⟨t,BB6.Agent47CRaw.path_reach p BB6CLine.Reach.init,ht,hupper,?_⟩
  intro X L hX hR hL
  have hlower := terminal_clock_lower X L n' w' t p' ht hX hR hL
  have hm := Nat.mul_le_mul_left (factor L) (show w'+2*(X+8)^2≤N+1+2*(X+8)^2 by omega)
  omega

#print axioms cheap_growth
#print axioms major_charge
#print axioms terminal_band_budget
#print axioms terminal_clock_lower
#print axioms raw_terminal_clock_bounds
end BB6.Agent12ResetLower
