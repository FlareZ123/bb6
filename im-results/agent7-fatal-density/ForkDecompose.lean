import SixPacketRoot
set_option maxHeartbeats 0
namespace CascadeFiveForced
open CascadeOddRay CascadeRayPeriod CascadeResetInverse

/-- The exact, untruncated odd-arm reset-predecessor grammar. -/
def OddParent (h u:Nat):Prop :=
  ∃ k t d, d%2=1 ∧
    (6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1) ∧
    2*u+5=3^(t+1)*d ∧
    2*(2^t*d)=8*2^k+h+k+5

/-- A high-band symbolic ray node has exactly the canonical even predecessor
    and all of the genuine odd-arm parents. No inverse exits are dropped. -/
theorem exact_fork_root_iff (n j:Nat) (hn:4≤n)
    (hm:CascadeOddRay.deficit n j≤2^n):
    (CascadeSweep.ReachC (2,0) (ray n j,0) ↔
      CascadeSweep.ReachC (2,0) (ray n (j+1),0) ∨
        ∃q, CascadeSweep.ReachC (2,0) (q,0) ∧ OddParent q (ray n j)) := by
  have hb:=ray_band n j hn hm
  have hnext:=ray_next_eq n j hn hm
  have hne:ray n j≠2:=by
    have hp:1≤2^n:=Nat.one_le_pow n 2 (by decide)
    omega
  constructor
  · intro hr
    have hc:ResetChain 2 (ray n j):=(root_reset_chain_iff (ray n j)).mp hr
    obtain ⟨q,hchain,hparent⟩:=CascadeUniformFatal.reset_chain_last hc hne
    rcases hparent with ⟨k,hbk,heq⟩ | hodd
    · have hk:k=n-1:=CascadeUniformFatal.even_band_scale_unique
          (ray n j) k (n-1) hbk ⟨hb.2.2.1,hb.2.2.2⟩
      have hq:q=ray n (j+1):=by rw[hk] at heq;omega
      rw[hq] at hchain
      exact Or.inl ((root_reset_chain_iff _).mpr hchain)
    · exact Or.inr ⟨q,(root_reset_chain_iff _).mpr hchain,hodd⟩
  · rintro (hr|⟨q,hq,ho⟩)
    · have hc:ResetChain 2 (ray n (j+1)):=(root_reset_chain_iff _).mp hr
      exact (root_reset_chain_iff _).mpr
        (ResetChain.append hc (Or.inl ⟨n-1,⟨hb.2.2.1,hb.2.2.2⟩,hnext⟩))
    · have hc:ResetChain 2 q:=(root_reset_chain_iff _).mp hq
      exact (root_reset_chain_iff _).mpr
        (ResetChain.append hc (Or.inr ho))

/-- The existence of an odd fork at a high-band ray node requires the precise
    divisible-by-nine signed numerator obstruction. -/
theorem odd_fork_requires_nine (n j q:Nat) (hn:4≤n)
    (hm:CascadeOddRay.deficit n j≤2^n)
    (ho:OddParent q (ray n j)) :
    signedZ n j%9=0:=by
  obtain ⟨k,t,d,hd,hb,hout,heq⟩:=ho
  have hband:=ray_band n j hn hm
  by_cases ht:t=0
  · subst t
    have hbad := CascadeAgent10Four.near_top_no_odd_tzero
       (ray n j) n hn hband.1 hband.2.1
       ⟨k,d,by simpa using hb,by simpa using hout⟩
    exact False.elim hbad
  · have ht1:1≤t:=by omega
    have hmod:3^(t+1)%9=0:=by
      have he:t+1=2+(t-1):=by omega
      rw[he,Nat.pow_add]
      simp
    have hnat:(2*ray n j+5)%9=0:=by
      rw[hout,Nat.mul_mod,hmod]
      simp
    have hnum:=signed_ray_eq_numerator n j hn hm
    rw[hnum]
    exact_mod_cast hnat

/-- Express the authentic true-root question at ray depth j. -/
def rootedAt (n j:Nat):Prop :=
  CascadeSweep.ReachC (2,0) (ray n j,0)

def oddRootAt (n j:Nat):Prop :=
  ∃q, CascadeSweep.ReachC (2,0) (q,0) ∧ OddParent q (ray n j)

private theorem root_edge_succ (n j:Nat) (h:rootEdge n j):
    rootedAt n j ↔ rootedAt n (j+1) := by
  exact h

/-- The complete source-authentic six-ray packet is exactly one canonical
    continuation plus all odd-parent root branches at a single even depth.
    The allowed fork depth is 0, 2 or 4. -/
theorem exact_six_packet_fork (n j:Nat) (hn:4≤n)
    (hsector:n%6=4 ∨ n%6=5) (hpar:j%2=0)
    (hband:deficit n (j+5)≤2^n):
    ∃i, (i=0 ∨ i=2 ∨ i=4) ∧
      (rootedAt n j ↔ rootedAt n (j+6) ∨ oddRootAt n (j+i)) := by
  have hh:=five_of_six_root_edges n j hn hsector hpar hband
  have hm0:=deficit_packet_bound n j 0 (by omega) hband
  have hm2:=deficit_packet_bound n j 2 (by omega) hband
  have hm4:=deficit_packet_bound n j 4 (by omega) hband
  rcases hh with ⟨h1,h2,h3,h4,h5⟩ | ⟨h0,h1,h3,h4,h5⟩ |
      ⟨h0,h1,h2,h3,h5⟩
  · refine ⟨0,Or.inl rfl,?_⟩
    have hf:=exact_fork_root_iff n j hn hm0
    dsimp [rootedAt,oddRootAt]
    dsimp [rootEdge] at h1 h2 h3 h4 h5
    rw [hf,h1,h2,h3,h4,h5]
  · refine ⟨2,Or.inr (Or.inl rfl),?_⟩
    have hf:=exact_fork_root_iff n (j+2) hn hm2
    dsimp [rootedAt,oddRootAt]
    dsimp [rootEdge] at h0 h1 h3 h4 h5
    rw [h0,h1,hf,h3,h4,h5]
  · refine ⟨4,Or.inr (Or.inr rfl),?_⟩
    have hf:=exact_fork_root_iff n (j+4) hn hm4
    dsimp [rootedAt,oddRootAt]
    dsimp [rootEdge] at h0 h1 h2 h3 h5
    rw [h0,h1,h2,h3,hf,h5]

#print axioms exact_fork_root_iff
#print axioms odd_fork_requires_nine
#print axioms exact_six_packet_fork
end CascadeFiveForced
