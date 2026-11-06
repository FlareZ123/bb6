import RayThirdGate
set_option maxHeartbeats 0
namespace CascadeRayThirdNoRoot
open CascadeResetInverse CascadeSweep CascadeRayOddStrip
open CascadeRayTwoGate CascadeRayThirdGeometry CascadeRayThirdGate

private theorem pow_period_six_mod3 (n:Nat):2^(n+6)%3=2^n%3:=by
  rw[Nat.pow_add]
  simp[Nat.mul_mod]

private theorem pow_mod_six_mod3 (n:Nat):2^n%3=2^(n%6)%3:=by
  induction n using Nat.strongRecOn with
  | ind n ih=>
    by_cases hn:n<6
    · simp[Nat.mod_eq_of_lt hn]
    · have hm:n-6<n:=by omega
      have he:n=(n-6)+6:=by omega
      rw[he,pow_period_six_mod3,ih (n-6) hm]
      have hh:((n-6)+6)%6=(n-6)%6:=by omega
      rw[hh]

private theorem coefficient_mod (n:Nat) (hn:20≤n)
  (hsector:n%6=4 ∨ n%6=5):
  (8*2^(n-4)+(n-4))%3=2:=by
  have hp:=pow_mod_six_mod3 (n-4)
  rcases hsector with h4|h5
  · have hk:(n-4)%6=0:=by omega
    have hm:2^(n-4)%3=1:=by rw[hp,hk]
    omega
  · have hk:(n-4)%6=1:=by omega
    have hm:2^(n-4)%3=2:=by rw[hp,hk]
    omega

private theorem odd_band_unique (u k l:Nat)
  (ha:6*2^k+1≤u ∧ u≤8*2^k-1)
  (hb:6*2^l+1≤u ∧ u≤8*2^l-1):k=l:=by
  by_cases he:k=l
  · exact he
  by_cases hk:k<l
  · have hp:2^(k+1)≤2^l:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    rw[Nat.pow_succ] at hp
    omega
  · have hp:2^(l+1)≤2^k:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    rw[Nat.pow_succ] at hp
    omega

private theorem third_scale (n D h w d k:Nat) (hn:20≤n)
  (hm:2048*D+16384*n+16384≤2^n)
  (hl:9*h+8*D+9*n+7=14*2^n)
  (hw:2*h=2*2^n+w+(n-2))
  (hz:2*w+5=9*d)
  (hb:6*2^k+1≤2*d ∧ 2*d≤8*2^k-1):k=n-4:=by
  have hp:2^n=16*2^(n-4):=by
    have he:n=(n-4)+4:=by omega
    calc
      2^n=2^((n-4)+4):=congrArg (fun x:Nat=>2^x) he
      _=16*2^(n-4):=by rw[Nat.pow_add];omega
  have hband:6*2^(n-4)+1≤2*d ∧ 2*d≤8*2^(n-4)-1:=by constructor <;> omega
  exact odd_band_unique (2*d) k (n-4) hb hband

/-- New uniform 3-adic second-generation exclusion. When the middle-gap
    predecessor w has exactly its t=1 odd inverse g and g%3 is 0 or 1,
    the next four forced even resets end in a second dyadic gap.
    All relevant inverse arms and their true-blank root are retained. -/
theorem offray_third_gate_dead (n D h w d g:Nat) (hn:20≤n)
  (hsector:n%6=4 ∨ n%6=5)
  (hm:2048*D+16384*n+16384≤2^n)
  (hl:9*h+8*D+9*n+7=14*2^n)
  (hw:2*h=2*2^n+w+(n-2))
  (hdiv:(2*h+5)%27≠0)
  (wdiv:(2*w+5)%27≠0)
  (hz:2*w+5=9*d)
  (hg:4*d=8*2^(n-4)+g+(n-4)+5)
  (hgmod:g%3≠2):
  ¬ReachC (2,0) (h,0):=by
  let p:=2^(n-4)
  let e:=8*p+(n-4)
  let g1:=2*g-e
  let g2:=4*g-3*e
  let g3:=8*g-7*e
  let g4:=16*g-15*e
  obtain ⟨hb0,hb1,hb2,hb3,hgap,he0,he1,he2,he3⟩:=
    four_forced_geometry n D h w d g hn hm hl hw hz hg
  have hemod:e%3=2:=coefficient_mod n hn hsector
  have hnotg:¬ReachC (2,0) (g,0):=
    four_even_no_root n g g1 g2 g3 g4 hn hemod hgmod
      hb0 hb1 hb2 hb3 hgap (by omega)
      (by omega)
      (by omega)
      (by omega)
  have hmargin:32*D+64*n+128≤2^n:=by omega
  intro hr
  have hroot:=((offray_fork_root_iff_second_tone n D h w
    (by omega) hmargin hl hw hdiv wdiv)).mp hr
  obtain ⟨q,k,d',hqroot,hdodd,hband,hz',hfrom⟩:=hroot
  have hd_eq:d'=d:=by omega
  have hk:k=n-4:=third_scale n D h w d' k hn hm hl hw hz' hband
  have hq_eq:q=g:=by rw[hk,hd_eq] at hfrom;omega
  subst q
  exact hnotg hqroot


/-- For the surviving fatal-index sectors, the second t=1 odd-parent
    residue condition follows automatically from its exact 3-adic
    valuation one. All high-margin two-tier valuation-one forks die. -/
theorem offray_third_gate_dead_auto (n D h w d g:Nat) (hn:20≤n)
  (hsector:n%6=4 ∨ n%6=5)
  (hm:2048*D+16384*n+16384≤2^n)
  (hl:9*h+8*D+9*n+7=14*2^n)
  (hw:2*h=2*2^n+w+(n-2))
  (hdiv:(2*h+5)%27≠0)
  (wdiv:(2*w+5)%27≠0)
  (hz:2*w+5=9*d)
  (hg:4*d=8*2^(n-4)+g+(n-4)+5):
  ¬ReachC (2,0) (h,0):=by
  have hemod:=coefficient_mod n hn hsector
  have hdmod:d%3≠0:=by
    intro hdzero
    have hzero:(9*d)%27=0:=by omega
    rw[←hz] at hzero
    exact wdiv hzero
  have hgmod:g%3≠2:=by omega
  exact offray_third_gate_dead n D h w d g hn hsector hm hl hw
    hdiv wdiv hz hg hgmod


/-- Full blank-root exclusion without assuming any independently supplied
    second odd parent. A hypothetical root path constructs that parent
    by the source-exact inverse iff, and four forced even returns
    exclude it in the second dyadic gap. -/
theorem offray_fork_dead_both_valuation_one (n D h w:Nat) (hn:20≤n)
  (hsector:n%6=4 ∨ n%6=5)
  (hm:2048*D+16384*n+16384≤2^n)
  (hl:9*h+8*D+9*n+7=14*2^n)
  (hw:2*h=2*2^n+w+(n-2))
  (hdiv:(2*h+5)%27≠0)
  (wdiv:(2*w+5)%27≠0):
  ¬ReachC (2,0) (h,0):=by
  have hm0:32*D+64*n+128≤2^n:=by omega
  intro hr
  have hrw:(ReachC (2,0) (w,0)):=
    (offray_fork_root_iff_even n D h w (by omega) hm0 hl hw hdiv).mp hr
  obtain ⟨hb,hnear,hodd,hgap⟩:=
    CascadeRayOddStrip.ray_offfork_geometry n D h w (by omega) hm0 hl hw
  have hu:8*w+32<9*2^n:=by omega
  have hroot:∃(q k d:Nat), ReachC (2,0) (q,0) ∧
      d%2=1 ∧ (6*2^k+1≤2*d ∧ 2*d≤8*2^k-1) ∧
      2*w+5=9*d ∧ 4*d=8*2^k+q+k+5:=
    (CascadeRayGapTone.narrow_gap_root_iff_tone n w (by omega)
      hgap.1 hu wdiv).mp hrw
  obtain ⟨q,k,d,hq,hd,hband,hz,heq⟩:=hroot
  have hk:k=n-4:=third_scale n D h w d k hn hm hl hw hz hband
  have heqg:4*d=8*2^(n-4)+q+(n-4)+5:=by rw[hk] at heq;omega
  exact (offray_third_gate_dead_auto n D h w d q hn hsector
    hm hl hw hdiv wdiv hz heqg) hr

#print axioms offray_fork_dead_both_valuation_one

#print axioms offray_third_gate_dead_auto

#print axioms offray_third_gate_dead
end CascadeRayThirdNoRoot
