import ValuationFullCount
import Lean.Elab.Tactic.Omega

namespace BB6.Agent34Valuation
open BB6.Agent46

theorem even_source_sum_parity (a x y n : Nat)
    (hsum : x+y=2^n*(2*a+4)) :
    (x+y)%2=0 := by
  have hdiv : 2∣x+y := by
    rw [hsum]
    refine ⟨2^n*(a+2),?_⟩
    calc
      2^n*(2*a+4)=2^n*(2*(a+2)) := by congr 1 <;> omega
      _=2*(2^n*(a+2)) := by ac_rfl
  obtain ⟨w,hw⟩ := hdiv
  omega

theorem odd_source_sum_parity (a x y n : Nat)
    (hsum : x+y+1=2^n*(2*a+6)) :
    (x+y)%2=1 := by
  have hdiv : 2∣x+y+1 := by
    rw [hsum]
    refine ⟨2^n*(a+3),?_⟩
    calc
      2^n*(2*a+6)=2^n*(2*(a+3)) := by congr 1 <;> omega
      _=2*(2^n*(a+3)) := by ac_rfl
  obtain ⟨w,hw⟩ := hdiv
  omega

theorem direct_parent_mem_candidates (a k x y : Nat)
    (ha : 2≤a) (hk : 0<k) (hbelow : 2*k≤a)
    (hedge : secNext (a,k)=some (x,y)) :
    (a,k)∈directExactCandidates x y := by
  have ha0 : a≠0 := by omega
  have ha1 : a≠1 := by omega
  have hk0 : k≠0 := by omega
  have hp := (section_preimage_all_iff a k x y).mp hedge
  simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
    if_neg hk0,if_pos hbelow] at hp
  rcases hp with ⟨hx,hy⟩
  have hpar : y%2=0 := by omega
  have hxsum : x+2*k=a := by
    rw [hx]
    exact Nat.sub_add_cancel hbelow
  have hsum : x+y=a+2 := by
    rw [hy]
    omega
  have haeq : a=x+y-2 := by
    rw [hsum]
    omega
  have hy2 : y-2=2*k := by omega
  have hkeq : k=(y-2)/2 := by
    rw [hy2]
    exact (Nat.mul_div_cancel_left k (by decide : 0<2)).symm
  have hcoord : a=x+y-2 ∧ k=(y-2)/2 := ⟨haeq,hkeq⟩
  have hsource : secNext (x+y-2,(y-2)/2)=some (x,y) := by
    simpa [hcoord.1,hcoord.2] using hedge
  unfold directExactCandidates
  simp [hpar,hsource]

theorem zero_parent_sum_even (k x y : Nat)
    (hy : 5≤y) (hedge : secNext (0,k)=some (x,y)) :
    (x+y)%2=0 := by
  have hk0 : k≠0 := by
    intro hk
    have h0 : secNext (0,0)=some (x,y) := by simpa [hk] using hedge
    have hp := (section_preimage_all_iff 0 0 x y).mp h0
    simp [sectionPreimageAll] at hp
  have hk1 : k≠1 := by
    intro hk
    have h1 : secNext (0,1)=some (x,y) := by simpa [hk] using hedge
    have hp := (section_preimage_all_iff 0 1 x y).mp h1
    simp [sectionPreimageAll] at hp
    rcases hp with ⟨hx,hy4⟩
    omega
  have hp := (section_preimage_all_iff 0 k x y).mp hedge
  simp only [sectionPreimageAll,if_neg hk0,if_neg hk1] at hp
  obtain ⟨_,n,hs,_⟩ := hp
  have hdiv : 2∣x+y := by
    rw [hs]
    refine ⟨2^n*4,?_⟩
    calc
      2^n*8=2^n*(2*4) := by congr 1 <;> omega
      _=2*(2^n*4) := by ac_rfl
  obtain ⟨w,hw⟩ := hdiv
  omega

theorem one_parent_sum_odd (k x y : Nat)
    (hy : 5≤y) (hedge : secNext (1,k)=some (x,y)) :
    (x+y)%2=1 := by
  by_cases hk0 : k=0
  · have h0 : secNext (1,0)=some (x,y) := by simpa [hk0] using hedge
    have hp := (section_preimage_all_iff 1 0 x y).mp h0
    simp [sectionPreimageAll] at hp
    rcases hp with ⟨hx,hy1⟩
    omega
  by_cases hk1 : k=1
  · have h1 : secNext (1,1)=some (x,y) := by simpa [hk1] using hedge
    have hp := (section_preimage_all_iff 1 1 x y).mp h1
    simp [sectionPreimageAll] at hp
    rcases hp with ⟨hx,hy3⟩
    omega
  by_cases hk2 : k=2
  · have h2 : secNext (1,2)=some (x,y) := by simpa [hk2] using hedge
    have hp := (section_preimage_all_iff 1 2 x y).mp h2
    simp [sectionPreimageAll] at hp
    rcases hp with ⟨hx,hy5⟩
    omega
  by_cases hk3 : k=3
  · have h3 : secNext (1,3)=some (x,y) := by simpa [hk3] using hedge
    have hp := (section_preimage_all_iff 1 3 x y).mp h3
    simp [sectionPreimageAll] at hp
    rcases hp with ⟨hx,hy7⟩
    omega
  have hp := (section_preimage_all_iff 1 k x y).mp hedge
  simp only [sectionPreimageAll,if_neg (by decide : (1:Nat)≠0),
    if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at hp
  rcases hp with ⟨hy3,_⟩ | ⟨_,n,hs,_⟩
  · omega
  · have hdiv : 2∣x+y+1 := by
      rw [hs]
      refine ⟨2^n*8,?_⟩
      calc
        2^n*16=2^n*(2*8) := by congr 1 <;> omega
        _=2*(2^n*8) := by ac_rfl
    obtain ⟨w,hw⟩ := hdiv
    omega

theorem zero_parent_mem_candidates (k x y v u : Nat)
    (hy : 5≤y) (hfact : x+y=2^v*(2*u+1))
    (hedge : secNext (0,k)=some (x,y)) :
    (0,k)∈zeroExactCandidates x y v u := by
  have hk0 : k≠0 := by
    intro hk
    have h0 : secNext (0,0)=some (x,y) := by simpa [hk] using hedge
    have hp := (section_preimage_all_iff 0 0 x y).mp h0
    simp [sectionPreimageAll] at hp
  have hk1 : k≠1 := by
    intro hk
    have h1 : secNext (0,1)=some (x,y) := by simpa [hk] using hedge
    have hp := (section_preimage_all_iff 0 1 x y).mp h1
    simp [sectionPreimageAll] at hp
    omega
  have hp := (section_preimage_all_iff 0 k x y).mp hedge
  simp only [sectionPreimageAll,if_neg hk0,if_neg hk1] at hp
  obtain ⟨_,n,hs,hc⟩ := hp
  have hpow : 2^(n+3)=2^v*(2*u+1) := by
    calc
      2^(n+3)=2^n*2^3 := by rw [Nat.pow_add]
      _=2^n*8 := by rw [show (2:Nat)^3=8 by decide]
      _=x+y := hs.symm
      _=2^v*(2*u+1) := hfact
  obtain ⟨hv,hu⟩ := pow2_odd_factor_unique (n+3) v u hpow
  have hcost : 2*k+9+3*n=x+2*y := by omega
  have hcoord : zeroParentAtValuation x y v=(0,k) := by
    simp [zeroParentAtValuation,hv]
    omega
  have hcond : u=0 ∧ 3≤v ∧
      secNext (zeroParentAtValuation x y v)=some (x,y) := by
    refine ⟨hu,by omega,?_⟩
    calc
      secNext (zeroParentAtValuation x y v)=secNext (0,k) :=
        congrArg secNext hcoord
      _=some (x,y) := hedge
  unfold zeroExactCandidates
  simp [hcond]

theorem one_parent_mem_candidates (k x y v u : Nat)
    (hy : 5≤y) (hfact : x+y+1=2^v*(2*u+1))
    (hedge : secNext (1,k)=some (x,y)) :
    (1,k)∈oneExactCandidates x y v u := by
  by_cases hk0 : k=0
  · have h0 : secNext (1,0)=some (x,y) := by simpa [hk0] using hedge
    have hp := (section_preimage_all_iff 1 0 x y).mp h0
    simp [sectionPreimageAll] at hp
    omega
  by_cases hk1 : k=1
  · have h1 : secNext (1,1)=some (x,y) := by simpa [hk1] using hedge
    have hp := (section_preimage_all_iff 1 1 x y).mp h1
    simp [sectionPreimageAll] at hp
    rcases hp with ⟨hx,hy3⟩
    omega
  by_cases hk2 : k=2
  · have h2 : secNext (1,2)=some (x,y) := by simpa [hk2] using hedge
    have hp := (section_preimage_all_iff 1 2 x y).mp h2
    simp [sectionPreimageAll] at hp
    rcases hp with ⟨hx,hy5⟩
    have hpow : 2^3=2^v*(2*u+1) := by
      calc
        2^3=8 := by decide
        _=x+y+1 := by omega
        _=2^v*(2*u+1) := hfact
    obtain ⟨hv,hu⟩ := pow2_odd_factor_unique 3 v u hpow
    have hcond : x=2 ∧ y=5 ∧ secNext (1,2)=some (x,y) :=
      ⟨hx,hy5,h2⟩
    unfold oneExactCandidates
    simp [hcond,hv,hu,hk2]
  by_cases hk3 : k=3
  · have h3 : secNext (1,3)=some (x,y) := by simpa [hk3] using hedge
    have hp := (section_preimage_all_iff 1 3 x y).mp h3
    simp [sectionPreimageAll] at hp
    rcases hp with ⟨hx,hy7⟩
    have hpow : 2^3=2^v*(2*u+1) := by
      calc
        2^3=8 := by decide
        _=x+y+1 := by omega
        _=2^v*(2*u+1) := hfact
    obtain ⟨hv,hu⟩ := pow2_odd_factor_unique 3 v u hpow
    have hcond : x=0 ∧ y=7 ∧ secNext (1,3)=some (x,y) :=
      ⟨hx,hy7,h3⟩
    unfold oneExactCandidates
    simp [hcond,hv,hu,hk3]
  have hp := (section_preimage_all_iff 1 k x y).mp hedge
  simp only [sectionPreimageAll,if_neg (by decide : (1:Nat)≠0),
    if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at hp
  rcases hp with ⟨hy3,_⟩ | ⟨_,n,hs,hc⟩
  · omega
  · have hpow : 2^(n+4)=2^v*(2*u+1) := by
      calc
        2^(n+4)=2^n*2^4 := by rw [Nat.pow_add]
        _=2^n*16 := by rw [show (2:Nat)^4=16 by decide]
        _=x+y+1 := hs.symm
        _=2^v*(2*u+1) := hfact
    obtain ⟨hv,hu⟩ := pow2_odd_factor_unique (n+4) v u hpow
    have hcost : 2*k+11+3*n=x+2*y := by omega
    have hcoord : oneParentAtValuation x y v=(1,k) := by
      simp [oneParentAtValuation,hv]
      omega
    have hcond : u=0 ∧ 4≤v ∧
        secNext (oneParentAtValuation x y v)=some (x,y) := by
      refine ⟨hu,by omega,?_⟩
      calc
        secNext (oneParentAtValuation x y v)=secNext (1,k) :=
          congrArg secNext hcoord
        _=some (x,y) := hedge
    unfold oneExactCandidates
    simp [hcond]

theorem even_sum_parent_mem_fullCandidates (a k x y v u : Nat)
    (hy : 5≤y) (hS : (x+y)%2=0)
    (hfact : x+y=2^v*(2*u+1))
    (hedge : secNext (a,k)=some (x,y)) :
    (a,k)∈evenFullCandidates x y v u := by
  by_cases ha0 : a=0
  · subst a
    apply List.mem_append.mpr
    right
    exact zero_parent_mem_candidates k x y v u hy hfact hedge
  by_cases ha1 : a=1
  · subst a
    have hodd := one_parent_sum_odd k x y hy hedge
    omega
  by_cases hk0 : k=0
  · have h0 : secNext (a,0)=some (x,y) := by simpa [hk0] using hedge
    have hp := (section_preimage_all_iff a 0 x y).mp h0
    simp [sectionPreimageAll,ha0,ha1] at hp
    omega
  by_cases hbelow : 2*k≤a
  · apply List.mem_append.mpr
    left
    apply List.mem_append.mpr
    right
    exact direct_parent_mem_candidates a k x y (by omega) (by omega) hbelow hedge
  · by_cases heven : a%2=0
    · apply List.mem_append.mpr
      left
      apply List.mem_append.mpr
      left
      exact even_high_parent_mem_exact_candidates a k x y v u
        (by omega) (by omega) (by omega) heven hy hfact hedge
    · have hodd : a%2=1 := by
        have hmod := Nat.mod_two_eq_zero_or_one a
        omega
      obtain ⟨n,hsum,_⟩ :=
        odd_high_parent_equations a k x y (by omega) (by omega)
          (by omega) hodd hy hedge
      have hSodd := odd_source_sum_parity a x y n hsum
      omega

theorem odd_sum_parent_mem_fullCandidates (a k x y v u : Nat)
    (hy : 5≤y) (hS : (x+y)%2=1)
    (hfact : x+y+1=2^v*(2*u+1))
    (hedge : secNext (a,k)=some (x,y)) :
    (a,k)∈oddFullCandidates x y v u := by
  by_cases ha0 : a=0
  · subst a
    have heven := zero_parent_sum_even k x y hy hedge
    omega
  by_cases ha1 : a=1
  · subst a
    apply List.mem_append.mpr
    right
    exact one_parent_mem_candidates k x y v u hy hfact hedge
  by_cases hk0 : k=0
  · have h0 : secNext (a,0)=some (x,y) := by simpa [hk0] using hedge
    have hp := (section_preimage_all_iff a 0 x y).mp h0
    simp [sectionPreimageAll,ha0,ha1] at hp
    omega
  by_cases hbelow : 2*k≤a
  · apply List.mem_append.mpr
    left
    apply List.mem_append.mpr
    right
    exact direct_parent_mem_candidates a k x y (by omega) (by omega) hbelow hedge
  · by_cases heven : a%2=0
    · obtain ⟨n,hsum,_⟩ :=
        even_high_parent_equations a k x y (by omega) (by omega)
          (by omega) heven hy hedge
      have hSeven := even_source_sum_parity a x y n hsum
      omega
    · have hodd : a%2=1 := by
        have hmod := Nat.mod_two_eq_zero_or_one a
        omega
      apply List.mem_append.mpr
      left
      apply List.mem_append.mpr
      left
      exact odd_high_parent_mem_exact_candidates a k x y v u
        (by omega) (by omega) (by omega) hodd hy hfact hedge

#print axioms even_sum_parent_mem_fullCandidates
#print axioms odd_sum_parent_mem_fullCandidates

end BB6.Agent34Valuation
