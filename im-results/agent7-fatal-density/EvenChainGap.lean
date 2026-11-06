import UniqueEvenBand
set_option maxHeartbeats 0
namespace CascadeEvenChainGap
open CascadeResetInverse CascadeSweep CascadeUniformFatal

private def inBand (k u:Nat) : Prop :=
  6*2^k-1≤u ∧ u≤8*2^k-3

/-- A formal even inverse walk at one fixed failed-sweep scale. -/
def evenWalk (k u:Nat) : Nat → Nat
  | 0 => u
  | j+1 => 2*evenWalk k u j-8*2^k-k

private theorem k_margin (k:Nat):k+2≤4*2^k:=by
  induction k with
  | zero=>decide
  | succ k ih=>
    rw[Nat.pow_succ]
    omega

private theorem walk_step (k u:Nat) (hb:inBand k u):
  2*u=8*2^k+evenWalk k u 1+k:=by
  have hk:=k_margin k
  dsimp [inBand] at hb
  have hp:0<2^k:=Nat.one_le_pow k 2 (by decide)
  simp only [evenWalk]
  omega

private theorem walk_succ (k u j:Nat)
  (hb:inBand k (evenWalk k u j)):
  2*evenWalk k u j = 8*2^k+evenWalk k u (j+1)+k:=by
  have hh:=walk_step k (evenWalk k u j) hb
  simpa [evenWalk] using hh

/-- A residue class is closed under repeated inverse even resets in
    the same dyadic scale, and never admits a source odd predecessor. -/
def SafeResidue (k u:Nat) : Prop :=
  u%3≠2 ∧ ((8*2^k+k)%3=2 ∨ u%3=(8*2^k+k)%3)

private theorem mod_step (k u v:Nat)
  (hs:SafeResidue k u)
  (he:2*u=8*2^k+v+k): SafeResidue k v:=by
  rcases hs with ⟨hu,hc|hc⟩
  · constructor
    · omega
    · exact Or.inl hc
  · have hv:v%3=(8*2^k+k)%3:=by omega
    exact ⟨by omega,Or.inr hv⟩

/-- A source-exact one-edge equivalence for any even image-band
    target whose mod-three residue excludes every odd inverse arm. -/
theorem band_root_iff (k u v:Nat)
  (hb:inBand k u) (hu:u%3≠2)
  (he:2*u=8*2^k+v+k):
  ReachC (2,0) (u,0) ↔ ReachC (2,0) (v,0):=by
  have hp:0<2^k:=Nat.one_le_pow k 2 (by decide)
  have hne:u≠2:=by omega
  constructor
  · intro hr
    have hc:ResetChain 2 u:=(root_reset_chain_iff u).mp hr
    obtain ⟨q,hqc,hq⟩:=reset_chain_last hc hne
    have hqeq:q=v:=any_parent_equals_even u k v q hb he hu hq
    rw[hqeq] at hqc
    exact (root_reset_chain_iff v).mpr hqc
  · intro hv
    have hc:ResetChain 2 v:=(root_reset_chain_iff v).mp hv
    have hp:ResetParent v u:=Or.inl ⟨k,hb,he⟩
    exact (root_reset_chain_iff u).mpr (ResetChain.append hc hp)

private theorem walk_mod (k u j:Nat)
 (hs:SafeResidue k u)
 (hb:∀i<j,inBand k (evenWalk k u i)):
 SafeResidue k (evenWalk k u j):=by
  induction j with
  | zero=>simpa [evenWalk] using hs
  | succ j ih=>
    have hj:SafeResidue k (evenWalk k u j):=
      ih (fun i hi => hb i (by omega))
    have hband:=hb j (by omega)
    exact mod_step k (evenWalk k u j) (evenWalk k u (j+1))
      hj (walk_succ k u j hband)

/-- Any source-valid run of j even inverse edges at one dyadic scale
    preserves *genuine* reachability in both directions for every j. -/
theorem walk_root_iff (k u j:Nat)
 (hs:SafeResidue k u)
 (hb:∀i<j,inBand k (evenWalk k u i)):
 ReachC (2,0) (u,0) ↔ ReachC (2,0) (evenWalk k u j,0):=by
  induction j with
  | zero=>simp [evenWalk]
  | succ j ih=>
    have hbefore:∀i<j,inBand k (evenWalk k u i):=
      fun i hi => hb i (by omega)
    have hmod:=walk_mod k u j hs hbefore
    have hband:=hb j (by omega)
    have heq:=walk_succ k u j hband
    exact (ih hbefore).trans (band_root_iff k (evenWalk k u j)
      (evenWalk k u (j+1)) hband hmod.1 heq)

/-- A scale-stable even inverse walk that exits into the genuine no-even-
    image gap is excluded from the real #746 blank reset orbit,
    uniformly in the unbounded number j of intermediate resets. -/
theorem walk_exits_gap_unreachable (k u j:Nat)
 (hk:1≤k)
 (hs:SafeResidue k u)
 (hb:∀i<j,inBand k (evenWalk k u i))
 (hl:4*2^k-3<evenWalk k u j)
 (hh:evenWalk k u j<6*2^k-1):
 ¬ReachC (2,0) (u,0):=by
  have hm:=(walk_mod k u j hs hb).1
  have hshift:(k+1)-1=k:=by omega
  have hgap:∀m,¬(6*2^m-1≤evenWalk k u j ∧
    evenWalk k u j≤8*2^m-3):=by
    intro m
    exact TerminalExit.no_even_band (k+1) m (evenWalk k u j)
      (by omega) (by simpa [hshift] using hl) (by simpa [hshift] using hh)
  have hno:=root_excludes_nonimage (evenWalk k u j) hm hgap
  exact fun hr=>hno ((walk_root_iff k u j hs hb).mp hr)

#print axioms band_root_iff
#print axioms walk_root_iff
#print axioms walk_exits_gap_unreachable
end CascadeEvenChainGap
