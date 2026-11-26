import ResetClockLower
import SectionReachEquivalence

namespace BB6.Agent12LiveRank
open BB6CLine BB6.Agent47ThinCounted BB6.Agent12ResetLower
set_option maxHeartbeats 0

theorem settle_fixed {s : State} (hs : boundary s) : settle s=s := by
  rcases s with ⟨a,k,c⟩
  rcases hs with (hc|⟨ha,hc⟩)|hc
  · change c=0 at hc; subst c; simp [settle,drain,finish]
  · change a=0 at ha; change 4≤c at hc; subst a
    obtain ⟨d,rfl⟩ : ∃ d,c=d+4 := ⟨c-4,by omega⟩
    simp [settle,drain,finish]
  · change c=2 at hc; subst c; simp [settle,drain,finish]

theorem settle_minor {s t : State} (hs : ¬boundary s) (h : nextC s=some t) : settle s=settle t := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · exact False.elim (hs (Or.inl (Or.inl rfl)))
  · simp only [nextC,Option.some.injEq] at h; subst t; simp [settle,drain,finish]
  · simp [nextC] at h
  · simp only [nextC,Option.some.injEq] at h; subst t
    simp [settle,drain,finish]
  · rcases a with _|a
    · exact False.elim (hs (Or.inl (Or.inr ⟨rfl,by simp⟩)))
    · simp only [nextC,Option.some.injEq] at h; subst t
      have h1 : d+4-3=d+1 := by omega
      have h2 : d+3-3=d := by omega
      have hm : min (a+1) (d+1)=min a d+1 := by omega
      unfold settle
      congr 1
      simp only [drain,h1,h2,hm,Prod.mk.injEq]; omega

theorem split_at_settle {n w : Nat} {s t : State} (p : Path n w s t) (ht : boundary t) :
    ∃ m v n' w', n=m+n' ∧ w=v+w' ∧ Path m v s (settle s) ∧ Path n' w' (settle s) t := by
  induction p with
  | nil =>
    rw [settle_fixed ht]
    exact ⟨0,0,0,0,rfl,rfl,Path.nil _,Path.nil _⟩
  | @cons n w s u t he p ih =>
    by_cases hs : boundary s
    · rw [settle_fixed hs]
      exact ⟨0,0,_,_,by omega,by omega,Path.nil _,Path.cons he p⟩
    · obtain ⟨m,v,n',w',hn,hw,hp,hq⟩ := ih ht
      have heq:=settle_minor hs he
      rw [heq]
      exact ⟨m+1,weight s+v,n',w',by omega,by omega,Path.cons he hp,hq⟩

theorem boundary_band_budget (X L n w : Nat) (s t : State)
    (p : Path n w s t) (hs : boundary s) (ht : boundary t)
    (hX : 64≤X) (hr : X≤rankC s) (hL : rankC t<2^L) :
    scale X*rankC t+8*scale X*depth s+factor L*stored t≤
      scale X*rankC s+8*scale X*depth t+factor L*(stored s+w) := by
  induction n using Nat.strongRecOn generalizing s w with
  | ind n ih =>
    cases p with
    | nil => simp
    | @cons n w s u t he p =>
      rcases hs with hm|hstop
      · obtain ⟨m,v,n',w',hn,hw,hp,hq⟩ := split_at_settle p ht
        have hj : jump s=some (settle u) := by simp [jump,he]
        obtain ⟨_,_,_,_,_,hb,hinc,_⟩ := jump_spec hm hj
        have h1:=jump_budget X L hm he hp hj hX hr (Nat.lt_of_le_of_lt (path_rank_mono (Path.cons he p)) hL)
        have h2:=ih n' (by omega) w' (settle u) hq hb (by omega)
        rw [hw]
        simp only [Nat.mul_add] at h1 h2 ⊢
        omega
      · rw [stop_of_c2 s hstop] at he; contradiction

theorem boundary_band_entry (X n w : Nat) (s t : State) (p : Path n w s t)
    (hs : boundary s) (ht : boundary t) (hl : rankC s≤X) (hh : X≤rankC t) :
    ∃ z n' w', boundary z ∧ X≤rankC z ∧ rankC z<X+8 ∧ w'≤w ∧ Path n' w' z t := by
  induction n using Nat.strongRecOn generalizing s w with
  | ind n ih =>
    by_cases hnow : X≤rankC s
    · exact ⟨s,n,w,hs,hnow,by omega,by omega,p⟩
    · cases p with
      | nil => omega
      | @cons n w s u t he p =>
        rcases hs with hm|hstop
        · obtain ⟨m,v,n',w',hn,hw,hp,hq⟩ := split_at_settle p ht
          have hj : jump s=some (settle u) := by simp [jump,he]
          obtain ⟨_,_,_,_,_,hb,hinc,hgap⟩ := jump_spec hm hj
          by_cases hcross : X≤rankC (settle u)
          · exact ⟨_,n',w',hb,hcross,by omega,by omega,hq⟩
          · obtain ⟨z',n'',w'',hb',h1,h2,h3,hp'⟩ := ih n' (by omega) w' (settle u) hq hb (by omega)
            exact ⟨z',n'',w'',hb',h1,h2,by omega,hp'⟩
        · rw [stop_of_c2 s hstop] at he; contradiction

theorem boundary_clock_lower (X L n w : Nat) (t : State)
    (p : Path n w (5,1,0) t) (ht : boundary t)
    (hX : 64≤X) (hR : X≤rankC t) (hL : rankC t<2^L) :
    scale X*rankC t≤scale X*(X+8+8*L)+factor L*(w+2*(X+8)^2) := by
  obtain ⟨z,n',w',hb,hr,hgap,hw,p'⟩ := boundary_band_entry X n w (5,1,0) t p (Or.inl (Or.inl rfl)) ht (by simp [rankC]; omega) hR
  have hbudget:=boundary_band_budget X L n' w' z t p' hb ht hX hr hL
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

theorem raw_live_rank_bound (t : State) (hr : Reach t) (ht : boundary t)
    (X L : Nat) (hX : 64≤X) (hR : X≤rankC t) (hL : rankC t<2^L) :
    ∃ N h, BB6Coverage.run BB6.Agent47CRaw.cMachine N BB6Coverage.blank =
      some (BB6.Agent47CRaw.embed h (BB6.Agent47CRaw.enc t)) ∧
      scale X*rankC t≤scale X*(X+8+8*L)+factor L*(N+2*(X+8)^2) := by
  obtain ⟨n,w,p⟩ := BB6.Agent47CRaw.reach_path hr
  have hrw:=BB6.Agent47CRaw.raw_blank_path p
  cases p with
  | nil => simp [rankC] at hR; omega
  | @cons n w s u t he p =>
    have hu : u=(5,1,0) := by
      exact Option.some.inj (he.symm.trans (by rfl))
    subst u
    obtain ⟨h,hraw⟩ := hrw
    refine ⟨_,h,hraw,?_⟩
    have hlower:=boundary_clock_lower X L n w t p ht hX hR hL
    have hm:=Nat.mul_le_mul_left (factor L)
      (show w+2*(X+8)^2≤12+(weight (5,0,1)+w)+2*(X+8)^2 by omega)
    omega

theorem live_section_86784452 (hr : Reach (954556,42914948,0)) :
    ∃ N h, 6747765517117253610≤N ∧
      BB6Coverage.run BB6.Agent47CRaw.cMachine N BB6Coverage.blank =
        some (BB6.Agent47CRaw.embed h (BB6.Agent47CRaw.enc (954556,42914948,0))) := by
  obtain ⟨N,h,hrun,hbound⟩ := raw_live_rank_bound (954556,42914948,0) hr
    (Or.inl (Or.inl rfl)) 57856296 27 (by decide) (by decide) (by decide)
  have hs : scale 57856296=52302359169369 := by decide
  have hf : factor 27=224 := by decide
  have hR : rankC (954556,42914948,0)=86784452 := by decide
  rw [hs,hf,hR] at hbound
  norm_num at hbound
  exact ⟨N,h,by omega,hrun⟩

theorem section_reach_live_bound
    (hr : BB6.Agent8Section.run BB6.Agent46.secNext 12396378 (some (5,1)) =
        some (954556,42914948)) :
    ∃ N h, 6747765517117253610≤N ∧
      BB6Coverage.run BB6.Agent47CRaw.cMachine N BB6Coverage.blank =
        some (BB6.Agent47CRaw.embed h (BB6.Agent47CRaw.enc (954556,42914948,0))) :=
  live_section_86784452 (BB6.Agent15.cLine_c0_reach_iff_section_reach.mp ⟨_,hr⟩)

#print axioms boundary_clock_lower
#print axioms raw_live_rank_bound
#print axioms section_reach_live_bound
end BB6.Agent12LiveRank
