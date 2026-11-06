import ValuationHighCount
import Lean.Elab.Tactic.Omega

namespace BB6.Agent34Valuation
open BB6.Agent46

/-- The direct low-input predecessor, when its even right counter is valid. -/
def directExactCandidates (x y : Nat) : List (Nat × Nat) :=
  if y%2=0 ∧ secNext (x+y-2,(y-2)/2)=some (x,y) then
    [(x+y-2,(y-2)/2)] else []

/-- The zero-first exceptional parent, reconstructed from the target's
2-adic valuation when the total mass is a pure power of two. -/
def zeroParentAtValuation (x y v : Nat) : Nat × Nat :=
  (0,(x+2*y-9-3*(v-3))/2)

/-- The one-first exceptional high parent. -/
def oneParentAtValuation (x y v : Nat) : Nat × Nat :=
  (1,(x+2*y-11-3*(v-4))/2)

/-- The exact exceptional list for an even total mass. -/
def zeroExactCandidates (x y v u : Nat) : List (Nat × Nat) :=
  if u=0 ∧ 3≤v ∧
      secNext (zeroParentAtValuation x y v)=some (x,y) then
    [zeroParentAtValuation x y v] else []

/-- The exact exceptional list for an odd total mass. The two small
one-first sources are kept separate from the high valuation branch. -/
def oneExactCandidates (x y v u : Nat) : List (Nat × Nat) :=
  if u=0 ∧ 4≤v ∧
      secNext (oneParentAtValuation x y v)=some (x,y) then
    [oneParentAtValuation x y v]
  else if x=2 ∧ y=5 ∧ secNext (1,2)=some (x,y) then
    [(1,2)]
  else if x=0 ∧ y=7 ∧ secNext (1,3)=some (x,y) then
    [(1,3)]
  else []

def evenFullCandidates (x y v u : Nat) : List (Nat × Nat) :=
  evenHighExactCandidates x y v ++
    directExactCandidates x y ++ zeroExactCandidates x y v u

def oddFullCandidates (x y v u : Nat) : List (Nat × Nat) :=
  oddHighExactCandidates x y v ++
    directExactCandidates x y ++ oneExactCandidates x y v u

theorem directExactCandidates_length (x y : Nat) :
    (directExactCandidates x y).length≤1 := by
  unfold directExactCandidates
  by_cases h : y%2=0 ∧ secNext (x+y-2,(y-2)/2)=some (x,y)
  · simp [h]
  · simp [h]

theorem zeroExactCandidates_length (x y v u : Nat) :
    (zeroExactCandidates x y v u).length≤1 := by
  unfold zeroExactCandidates
  by_cases h : u=0 ∧ 3≤v ∧
      secNext (zeroParentAtValuation x y v)=some (x,y)
  · simp [h]
  · simp [h]

theorem oneExactCandidates_length (x y v u : Nat) :
    (oneExactCandidates x y v u).length≤1 := by
  unfold oneExactCandidates
  by_cases h1 : u=0 ∧ 4≤v ∧
      secNext (oneParentAtValuation x y v)=some (x,y)
  · simp [h1]
  · by_cases h2 : x=2 ∧ y=5 ∧ secNext (1,2)=some (x,y)
    · have h1' : ¬(u=0 ∧ 4≤v ∧ secNext (oneParentAtValuation 2 5 v)=some (2,5)) := by
        simpa [h2.1,h2.2.1] using h1
      simp [h1',h2]
    · by_cases h3 : x=0 ∧ y=7 ∧ secNext (1,3)=some (x,y)
      · have h1' : ¬(u=0 ∧ 4≤v ∧ secNext (oneParentAtValuation 0 7 v)=some (0,7)) := by
          simpa [h3.1,h3.2.1] using h1
        simp [h1',h2,h3]
      · simp [h1,h2,h3]

theorem pow2_odd_factor_unique (n v u : Nat)
    (h : 2^n=2^v*(2*u+1)) : v=n ∧ u=0 := by
  have h1 : 2^v ∣ 2^n := ⟨2*u+1,h⟩
  have h2 : 2^n ∣ 2^v*(2*u+1) := by
    rw [h.symm]
    exact Nat.dvd_refl _
  have hvn : v≤n := pow2_odd_factor_le n v 0 (by simpa using h1)
  have hnv : n≤v := pow2_odd_factor_le v n u h2
  have hv : v=n := by omega
  subst n
  have hcancel : 2^v*1=2^v*(2*u+1) := by simpa using h
  have heq : 1=2*u+1 :=
    Nat.mul_left_cancel (Nat.pow_pos (by decide)) hcancel
  omega

theorem evenHighCandidates_length_sharp (x y v : Nat)
    (hv : v%2=0) (hx : x%2=0) :
    (evenHighCandidates x y v).length≤v/2-1 := by
  rw [evenHighCandidates,List.length_map]
  exact evenDepthCandidates_length_sharp v x hv hx

theorem oddHighCandidates_length_sharp (x y v : Nat)
    (hv : v%2=0) (hx : x%2=1) :
    (oddHighCandidates x y v).length≤v/2-1 := by
  rw [oddHighCandidates,List.length_map]
  exact oddDepthCandidates_length_sharp v x hv hx

theorem evenHighExactCandidates_length_sharp (x y v : Nat)
    (hv : v%2=0) (hx : x%2=0) :
    (evenHighExactCandidates x y v).length≤v/2-1 := by
  unfold evenHighExactCandidates
  exact Nat.le_trans (List.length_filter_le _ _)
    (evenHighCandidates_length_sharp x y v hv hx)

theorem oddHighExactCandidates_length_sharp (x y v : Nat)
    (hv : v%2=0) (hx : x%2=1) :
    (oddHighExactCandidates x y v).length≤v/2-1 := by
  unfold oddHighExactCandidates
  exact Nat.le_trans (List.length_filter_le _ _)
    (oddHighCandidates_length_sharp x y v hv hx)

/-- If the direct and zero-first exceptional parents both exist, the
valuation is even and the target's first coordinate is even. This is the
parity fact that saves one high-depth slot in the sharp total degree bound. -/
theorem zero_exception_direct_parity (x y v u : Nat)
    (hy : 5≤y) (hfact : x+y=2^v*(2*u+1))
    (hdirect : directExactCandidates x y ≠ [])
    (hzero : zeroExactCandidates x y v u ≠ []) :
    v%2=0 ∧ x%2=0 := by
  have hdir : y%2=0 ∧ secNext (x+y-2,(y-2)/2)=some (x,y) := by
    unfold directExactCandidates at hdirect
    by_cases h : y%2=0 ∧ secNext (x+y-2,(y-2)/2)=some (x,y)
    · exact h
    · simp [h] at hdirect
  have hz : u=0 ∧ 3≤v ∧
      secNext (zeroParentAtValuation x y v)=some (x,y) := by
    unfold zeroExactCandidates at hzero
    by_cases h : u=0 ∧ 3≤v ∧
        secNext (zeroParentAtValuation x y v)=some (x,y)
    · exact h
    · simp [h] at hzero
  let k := (x+2*y-9-3*(v-3))/2
  have hkedge : secNext (0,k)=some (x,y) := by
    simpa [k,zeroParentAtValuation] using hz.2.2
  have hk0 : k≠0 := by
    intro hk
    have hkedge0 : secNext (0,0)=some (x,y) := by simpa [k,hk] using hkedge
    have hp := (section_preimage_all_iff 0 0 x y).mp hkedge0
    simp [sectionPreimageAll] at hp
  have hk1 : k≠1 := by
    intro hk
    have hkedge1 : secNext (0,1)=some (x,y) := by simpa [k,hk] using hkedge
    have hp := (section_preimage_all_iff 0 1 x y).mp hkedge1
    simp [sectionPreimageAll] at hp
    omega
  have hp := (section_preimage_all_iff 0 k x y).mp hkedge
  simp only [sectionPreimageAll,if_neg hk0,if_neg hk1] at hp
  obtain ⟨_,n,hs,hc⟩ := hp
  have hpow : 2^(n+3)=2^v*(2*u+1) := by
    calc
      2^(n+3)=2^n*2^3 := by rw [Nat.pow_add]
      _=2^n*8 := by rw [show (2:Nat)^3=8 by decide]
      _=x+y := hs.symm
      _=2^v*(2*u+1) := hfact
  obtain ⟨hv,huzero⟩ := pow2_odd_factor_unique (n+3) v u hpow
  have hsumEven : 2∣x+y := by
    rw [hfact,huzero]
    simpa using Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨w,hw⟩ := hsumEven
  have hx : x%2=0 := by omega
  have hn : n%2=1 := by omega
  have hvEven : v%2=0 := by omega
  exact ⟨hvEven,hx⟩

/-- If the direct and one-first high exceptional parents both exist, the
valuation is even and the target's first coordinate is odd. -/
theorem one_exception_direct_parity (x y v u : Nat)
    (hy : 5≤y) (hfact : x+y+1=2^v*(2*u+1))
    (hdirect : directExactCandidates x y ≠ [])
    (hone : oneExactCandidates x y v u ≠ []) :
    v%2=0 ∧ x%2=1 := by
  have hdir : y%2=0 ∧ secNext (x+y-2,(y-2)/2)=some (x,y) := by
    unfold directExactCandidates at hdirect
    by_cases h : y%2=0 ∧ secNext (x+y-2,(y-2)/2)=some (x,y)
    · exact h
    · simp [h] at hdirect
  have hhigh : u=0 ∧ 4≤v ∧
      secNext (oneParentAtValuation x y v)=some (x,y) := by
    unfold oneExactCandidates at hone
    by_cases h1 : u=0 ∧ 4≤v ∧
        secNext (oneParentAtValuation x y v)=some (x,y)
    · exact h1
    · simp [h1] at hone
      by_cases h2 : x=2 ∧ y=5 ∧ secNext (1,2)=some (x,y)
      · rcases h2 with ⟨_,hy5,_⟩
        omega
      · by_cases h3 : x=0 ∧ y=7 ∧ secNext (1,3)=some (x,y)
        · rcases h3 with ⟨_,hy7,_⟩
          omega
        · simp [h1,h2,h3] at hone
  let k := (x+2*y-11-3*(v-4))/2
  have hkedge : secNext (1,k)=some (x,y) := by
    simpa [k,oneParentAtValuation] using hhigh.2.2
  have hk0 : k≠0 := by
    intro hk
    have hkedge0 : secNext (1,0)=some (x,y) := by simpa [k,hk] using hkedge
    have hp := (section_preimage_all_iff 1 0 x y).mp hkedge0
    simp [sectionPreimageAll] at hp
    omega
  have hk1 : k≠1 := by
    intro hk
    have hkedge1 : secNext (1,1)=some (x,y) := by simpa [k,hk] using hkedge
    have hp := (section_preimage_all_iff 1 1 x y).mp hkedge1
    simp [sectionPreimageAll] at hp
    omega
  have hk2 : k≠2 := by
    intro hk
    have hkedge2 : secNext (1,2)=some (x,y) := by simpa [k,hk] using hkedge
    have hp := (section_preimage_all_iff 1 2 x y).mp hkedge2
    simp [sectionPreimageAll] at hp
    omega
  have hk3 : k≠3 := by
    intro hk
    have hkedge3 : secNext (1,3)=some (x,y) := by simpa [k,hk] using hkedge
    have hp := (section_preimage_all_iff 1 3 x y).mp hkedge3
    simp [sectionPreimageAll] at hp
    omega
  have hp := (section_preimage_all_iff 1 k x y).mp hkedge
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
    obtain ⟨hv,huzero⟩ := pow2_odd_factor_unique (n+4) v u hpow
    have hsumOdd : 2∣x+y+1 := by
      rw [hfact,huzero]
      simpa using Nat.pow_dvd_pow 2 (by omega)
    obtain ⟨w,hw⟩ := hsumOdd
    have hx : x%2=1 := by omega
    have hn : n%2=0 := by omega
    have hvEven : v%2=0 := by omega
    exact ⟨hvEven,hx⟩

#print axioms pow2_odd_factor_unique
#print axioms zero_exception_direct_parity
#print axioms one_exception_direct_parity

end BB6.Agent34Valuation
