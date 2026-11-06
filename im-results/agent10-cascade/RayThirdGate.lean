import RayThirdGeometry
set_option maxHeartbeats 0
namespace CascadeRayThirdGate
open CascadeResetInverse CascadeSweep CascadeUniformFatal CascadeRayGapTone
open CascadeRayOddStrip CascadeRayTwoGate CascadeRayThirdGeometry

private theorem even_root_propagate (k u v:Nat)
  (hb:6*2^k-1≤u ∧ u≤8*2^k-3)
  (hmod:u%3≠2)
  (heq:2*u=8*2^k+v+k)
  (hnot:¬ReachC (2,0) (v,0)):
  ¬ReachC (2,0) (u,0):=by
  intro hr
  have hp:1≤2^k:=Nat.one_le_pow k 2 (by decide)
  have hne:u≠2:=by omega
  have hc:ResetChain 2 u:=(root_reset_chain_iff u).mp hr
  obtain ⟨q,hchain,hq⟩:=reset_chain_last hc hne
  have he:q=v:=any_parent_equals_even u k v q hb heq hmod hq
  subst q
  exact hnot ((root_reset_chain_iff v).mpr hchain)

private theorem even_mod_step (a b e:Nat)
  (hmod:a%3≠2) (hemod:e%3=2)
  (he:2*a=e+b):b%3≠2:=by omega

/-- Any scale-n-4 four-return even chain ending in the strict dyadic
    gap is blank-root impossible if its initial residue lies in {0,1}.
    Mod-three stability of each intermediate return is proved here. -/
theorem four_even_no_root (n g g1 g2 g3 g4:Nat) (hn:20≤n)
  (hemod:(8*2^(n-4)+(n-4))%3=2)
  (hgmod:g%3≠2)
  (hb0:6*2^(n-4)-1≤g ∧ g≤8*2^(n-4)-3)
  (hb1:6*2^(n-4)-1≤g1 ∧ g1≤8*2^(n-4)-3)
  (hb2:6*2^(n-4)-1≤g2 ∧ g2≤8*2^(n-4)-3)
  (hb3:6*2^(n-4)-1≤g3 ∧ g3≤8*2^(n-4)-3)
  (hg4:4*2^(n-4)-3<g4 ∧ g4<6*2^(n-4)-1)
  (he0:2*g=8*2^(n-4)+g1+(n-4))
  (he1:2*g1=8*2^(n-4)+g2+(n-4))
  (he2:2*g2=8*2^(n-4)+g3+(n-4))
  (he3:2*g3=8*2^(n-4)+g4+(n-4)):
  ¬ReachC (2,0) (g,0):=by
  have hm1:g1%3≠2:=even_mod_step g g1 _ hgmod hemod (by omega)
  have hm2:g2%3≠2:=even_mod_step g1 g2 _ hm1 hemod (by omega)
  have hm3:g3%3≠2:=even_mod_step g2 g3 _ hm2 hemod (by omega)
  have hm4:g4%3≠2:=even_mod_step g3 g4 _ hm3 hemod (by omega)
  have hs:n-3-1=n-4:=by omega
  have hnot4:¬ReachC (2,0) (g4,0):=
    root_excludes_nonimage g4 hm4 (fun m =>
      TerminalExit.no_even_band (n-3) m g4 (by omega)
        (by simpa only [hs] using hg4.1)
        (by simpa only [hs] using hg4.2))
  have hnot3:=even_root_propagate (n-4) g3 g4 hb3 hm3 he3 hnot4
  have hnot2:=even_root_propagate (n-4) g2 g3 hb2 hm2 he2 hnot3
  have hnot1:=even_root_propagate (n-4) g1 g2 hb1 hm1 he1 hnot2
  exact even_root_propagate (n-4) g g1 hb0 hgmod he0 hnot1

#print axioms four_even_no_root
end CascadeRayThirdGate
