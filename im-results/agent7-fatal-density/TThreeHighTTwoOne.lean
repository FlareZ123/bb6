import TThreeHighTTwoZero
import TThreeHighTTwoOneArithmetic
set_option maxHeartbeats 0
set_option maxRecDepth 8192

namespace CascadeHighTTwo
open CascadeSweep CascadeResetInverse CascadeUniformFatal CascadeForkOddDead CascadeOddRay CascadeTranslatedRayDepth

/-- The d=1 mod 3 four-even chain has alternating forced-even residues. -/
theorem mod_four_one (s k d a b c f g : Nat)
  (hconst:(8*s+k)%3=1) (hd:d%3=1)
  (h0:8*d=8*s+a+k+5)
  (h1:2*a=8*s+b+k)
  (h2:2*b=8*s+c+k)
  (h3:2*c=8*s+f+k)
  (h4:2*f=8*s+g+k) :
  a%3=2 ∧ b%3=0 ∧ c%3=2 ∧ f%3=0 ∧ g%3=2 := by omega

private theorem forced_parent_root_unique (x y:Nat) (hx:x≠2)
  (hun:∀w,ResetParent w x→w=y)
  (hroot:ReachC (2,0) (x,0)) : ReachC (2,0) (y,0) := by
  have hc:ResetChain 2 x := (root_reset_chain_iff x).mp hroot
  obtain ⟨v,hprev,hparent⟩ := reset_chain_last hc hx
  have hv : v=y := hun v hparent
  subst v
  exact (root_reset_chain_iff y).mpr hprev

/-- With both mod-nine odd gates absent, a rooted a forces the fourth even predecessor g to be rooted. -/
theorem four_even_one_root_continues (k a b c f g:Nat) (hk:10≤k)
  (hbandA:6*2^k-1≤a ∧ a≤8*2^k-3)
  (hbandB:6*2^k-1≤b ∧ b≤8*2^k-3)
  (hbandC:6*2^k-1≤c ∧ c≤8*2^k-3)
  (hbandF:6*2^k-1≤f ∧ f≤8*2^k-3)
  (he1:2*a=8*2^k+b+k)
  (he2:2*b=8*2^k+c+k)
  (he3:2*c=8*2^k+f+k)
  (he4:2*f=8*2^k+g+k)
  (hnot9A:(2*a+5)%9≠0) (hnot9C:(2*c+5)%9≠0)
  (hmodB:b%3≠2) (hmodF:f%3≠2)
  (hroot:ReachC (2,0) (a,0)) : ReachC (2,0) (g,0) := by
  have ha2:a≠2:=by omega
  have hb2:b≠2:=by omega
  have hc2:c≠2:=by omega
  have hf2:f≠2:=by omega
  have hbr := forced_parent_root_unique a b ha2
    (fun w hw=>band_nonine_parent_even k a b w (by omega) hbandA he1 hnot9A hw) hroot
  have hcr := forced_parent_root_unique b c hb2
    (fun w hw=>any_parent_equals_even b k c w hbandB he2 hmodB hw) hbr
  have hfr := forced_parent_root_unique c f hc2
    (fun w hw=>band_nonine_parent_even k c f w (by omega) hbandC he3 hnot9C hw) hcr
  exact forced_parent_root_unique f g hf2
    (fun w hw=>any_parent_equals_even f k g w hbandF he4 hmodF hw) hfr

/-- Exact source-C odd-parent witness for a rooted height in the even-image gap. -/
def GapOddParent (g:Nat) : Prop :=
  ∃x l t z, ReachC (2,0) (x,0) ∧ z%2=1 ∧
    6*2^l+1≤2^t*z ∧ 2^t*z≤8*2^l-1 ∧
    2*g+5=3^(t+1)*z ∧ 2*(2^t*z)=8*2^l+x+l+5

theorem gap_root_requires_odd_parent (k g:Nat) (hk:10≤k)
  (hgap:4*2^k<g ∧ 2*g+2<12*2^k)
  (hroot:ReachC (2,0) (g,0)) : GapOddParent g := by
  have hne:g≠2:=by omega
  have hc:ResetChain 2 g := (root_reset_chain_iff g).mp hroot
  obtain ⟨x,hprev,hparent⟩ := reset_chain_last hc hne
  rcases hparent with ⟨l,hband,heq⟩ | ⟨l,t,z,hd,hband,hnum,heq⟩
  · have hp:2^(k+2)=4*2^k:=by rw [Nat.pow_add]; omega
    have hgap':2^(k+2)<g ∧ 2*g+2<3*2^(k+2):=by rw [hp]; constructor <;> omega
    exact False.elim ((gap_avoids_even_images (k+2) g (by omega) hgap'.1 hgap'.2) l hband)
  · exact ⟨x,l,t,z,(root_reset_chain_iff x).mpr hprev,hd,hband.1,hband.2,hnum,heq⟩

/-- For a genuine high-q t=2 parent with d=1 mod 3, either one of two explicit 3-adic gates opens, or the fourth even ancestor g has a genuine odd source parent. -/
theorem high_ttwo_one_root_odd_fork (n j d0 q e r d a:Nat)
  (hn:20≤n) (hsector:n%6=4∨n%6=5)
  (hm:2048*deficit n j+16384*n+16384≤2^n)
  (hz:2*ray n j+5=81*d0)
  (hrel:16*d0=2^n+q+(n-3)+5)
  (hgate:2*q+5=81*e)
  (hrrel:16*e=8*2^(n-6)+r+(n-6)+5)
  (htwo:2*r+5=27*d)
  (he0:8*d=8*2^(n-8)+a+(n-8)+5)
  (hdmod:d%3=1) (hroot:ReachC (2,0) (a,0)) :
  ∃b c f g:Nat,
    2*a=8*2^(n-8)+b+(n-8) ∧
    2*b=8*2^(n-8)+c+(n-8) ∧
    2*c=8*2^(n-8)+f+(n-8) ∧
    2*f=8*2^(n-8)+g+(n-8) ∧
    ((2*a+5)%9=0 ∨ (2*c+5)%9=0 ∨ GapOddParent g) := by
  obtain ⟨hl,hu⟩:=high_source_ray_bounds n j d0 q e r hn hm hz hrel hgate hrrel
  obtain ⟨hdlo,hdhi⟩:=high_r_ttwo_interval n r d hn hl hu htwo
  have hs:=size_bound n hn
  obtain ⟨b,c,f,g,he1,he2,he3,he4⟩:=even_four_witnesses n (2^(n-8)) d a
    hn hs hdlo hdhi he0
  obtain ⟨ha,hb,hc,hf,hgap⟩:=even_four_geometry n (2^(n-8)) d a b c f g
    hn hs hdlo hdhi he0 he1 he2 he3 he4
  have hconst:=even_const_mod_three n hn hsector
  obtain ⟨haMod,hbMod,hcMod,hfMod,hgMod⟩:=mod_four_one (2^(n-8)) (n-8)
    d a b c f g hconst hdmod he0 he1 he2 he3 he4
  have hn18 : 18 ≤ n := Nat.le_trans (by decide : 18 ≤ 20) hn
  have hk : 10 ≤ n-8 := Nat.le_sub_of_add_le (by simpa using hn18)
  have hbmod : b%3≠2 := by rw [hbMod]; decide
  have hfmod : f%3≠2 := by rw [hfMod]; decide
  refine ⟨b,c,f,g,he1,he2,he3,he4,?_⟩
  by_cases ha9:(2*a+5)%9=0
  · exact Or.inl ha9
  · by_cases hc9:(2*c+5)%9=0
    · exact Or.inr (Or.inl hc9)
    · have hrootg:=four_even_one_root_continues (n-8) a b c f g hk
        ha hb hc hf he1 he2 he3 he4 ha9 hc9 hbmod hfmod hroot
      exact Or.inr (Or.inr (gap_root_requires_odd_parent (n-8) g hk hgap hrootg))

/-- Exact mod-9 selector: in each n mod 18 sector, the third d residue forces the odd fork at g. -/
theorem high_ttwo_one_mod9_or_gap_fork (n j d0 q e r d a:Nat)
  (hn:20≤n) (hsector:n%6=4∨n%6=5)
  (hm:2048*deficit n j+16384*n+16384≤2^n)
  (hz:2*ray n j+5=81*d0)
  (hrel:16*d0=2^n+q+(n-3)+5)
  (hgate:2*q+5=81*e)
  (hrrel:16*e=8*2^(n-6)+r+(n-6)+5)
  (htwo:2*r+5=27*d)
  (he0:8*d=8*2^(n-8)+a+(n-8)+5)
  (hdmod:d%3=1) (hroot:ReachC (2,0) (a,0)) :
  ∃b c f g:Nat,
    2*a=8*2^(n-8)+b+(n-8) ∧
    2*b=8*2^(n-8)+c+(n-8) ∧
    2*c=8*2^(n-8)+f+(n-8) ∧
    2*f=8*2^(n-8)+g+(n-8) ∧
    (((n%18=4∨n%18=17) → d%9=1∨d%9=4∨GapOddParent g) ∧
     ((n%18=5∨n%18=10) → d%9=4∨d%9=7∨GapOddParent g) ∧
     ((n%18=11∨n%18=16) → d%9=1∨d%9=7∨GapOddParent g)) := by
  obtain ⟨b,c,f,g,he1,he2,he3,he4,hbranch⟩ :=
    high_ttwo_one_root_odd_fork n j d0 q e r d a hn hsector hm hz hrel hgate hrrel htwo he0 hdmod hroot
  have hselector := CascadeHighTTwoArithmetic.one_gate_mod9_or_odd
    n (n-8) (2^(n-8)) d a b c (GapOddParent g) hn rfl rfl he0 he1 he2 hdmod hbranch
  exact ⟨b,c,f,g,he1,he2,he3,he4,hselector⟩

#print axioms mod_four_one
#print axioms four_even_one_root_continues
#print axioms gap_root_requires_odd_parent
#print axioms high_ttwo_one_root_odd_fork
#print axioms high_ttwo_one_mod9_or_gap_fork
end CascadeHighTTwo
