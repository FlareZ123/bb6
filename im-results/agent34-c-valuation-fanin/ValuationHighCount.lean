import ValuationSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent34Valuation
open BB6.Agent46

/-- The permitted even-input bounce depths, encoded by half-depths.
The source valuation theorem fixes the parity, so one half-depth
parameter enumerates each possible recursive depth. -/
def evenDepthLimit (v x : Nat) : Nat :=
  if x%2=0 ∧ v%2=0 then v/2-1 else v/2

def oddDepthLimit (v x : Nat) : Nat :=
  if x%2=1 ∧ v%2=0 then v/2-1 else v/2

def evenDepthCandidates (v x : Nat) : List Nat :=
  let p := if x%2=0 then 1 else 0
  (List.range (evenDepthLimit v x)).map (fun i => 2*i+p)

def oddDepthCandidates (v x : Nat) : List Nat :=
  let p := x%2
  (List.range (oddDepthLimit v x)).map (fun i => 2*i+p)

theorem evenDepthCandidates_length (v x : Nat) :
    (evenDepthCandidates v x).length ≤ v/2 := by
  unfold evenDepthCandidates evenDepthLimit
  rw [List.length_map,List.length_range]
  by_cases h : x%2=0 ∧ v%2=0
  · simp [h]
  · simp [h]

theorem oddDepthCandidates_length (v x : Nat) :
    (oddDepthCandidates v x).length ≤ v/2 := by
  unfold oddDepthCandidates oddDepthLimit
  rw [List.length_map,List.length_range]
  by_cases h : x%2=1 ∧ v%2=0
  · simp [h]
  · simp [h]

theorem evenDepthCandidates_length_sharp (v x : Nat)
    (hv : v%2=0) (hx : x%2=0) :
    (evenDepthCandidates v x).length ≤ v/2-1 := by
  unfold evenDepthCandidates evenDepthLimit
  rw [List.length_map,List.length_range]
  simp [hv,hx]

theorem oddDepthCandidates_length_sharp (v x : Nat)
    (hv : v%2=0) (hx : x%2=1) :
    (oddDepthCandidates v x).length ≤ v/2-1 := by
  unfold oddDepthCandidates oddDepthLimit
  rw [List.length_map,List.length_range]
  simp [hv,hx]

theorem evenDepthCandidates_mem (v x n : Nat)
    (hbound : n+2≤v) (hpar : (n+1)%2=x%2) :
    n∈evenDepthCandidates v x := by
  let p := if x%2=0 then 1 else 0
  have hrepr : n=2*(n/2)+p := by
    have hdiv := Nat.div_add_mod n 2
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx
    · have hn : n%2=1 := by omega
      simp [p,hx]
      omega
    · have hn : n%2=0 := by omega
      simp [p,hx]
      omega
  have hi : n/2 < evenDepthLimit v x := by
    unfold evenDepthLimit
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one v with hv | hv <;>
      simp [hx,hv] <;> omega
  unfold evenDepthCandidates
  apply List.mem_map.mpr
  exact ⟨n/2,List.mem_range.mpr hi,hrepr.symm⟩

theorem oddDepthCandidates_mem (v x n : Nat)
    (hbound : n+2≤v) (hpar : n%2=x%2) :
    n∈oddDepthCandidates v x := by
  let p := x%2
  have hrepr : n=2*(n/2)+p := by
    have hdiv := Nat.div_add_mod n 2
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx
    · have hn : n%2=0 := by omega
      simp [p,hx]
      omega
    · have hn : n%2=1 := by omega
      simp [p,hx]
      omega
  have hi : n/2 < oddDepthLimit v x := by
    unfold oddDepthLimit
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one v with hv | hv <;>
      simp [hx,hv] <;> omega
  unfold oddDepthCandidates
  apply List.mem_map.mpr
  exact ⟨n/2,List.mem_range.mpr hi,hrepr.symm⟩

/-- Reconstruct the unique even-first, even-right source candidate
at a given recursive bounce depth from its target coordinates. -/
def evenParentAtDepth (x y n : Nat) : Nat × Nat :=
  let a := (x+y)/2^(n+1)-2
  (a,(x+2*y-a-7-3*n)/2)

/-- Reconstruct the unique odd-first source candidate at a given
recursive bounce depth. -/
def oddParentAtDepth (x y n : Nat) : Nat × Nat :=
  let a := (x+y+1)/2^(n+1)-3
  (a,(x+2*y-a-7-3*n)/2)

theorem evenParentAtDepth_eq (x y a k n : Nat)
    (hsum : x+y=2^n*(2*a+4))
    (hcost : 2*k+a+7+3*n=x+2*y) :
    evenParentAtDepth x y n=(a,k) := by
  have hmul : x+y=2^(n+1)*(a+2) := by
    calc
      x+y=2^n*(2*a+4) := hsum
      _=2^n*(2*(a+2)) := by congr 1 <;> omega
      _=2^(n+1)*(a+2) := by rw [Nat.pow_succ]; ac_rfl
  have hdiv : (x+y)/2^(n+1)=a+2 := by
    rw [hmul]
    exact Nat.mul_div_cancel_left (a+2) (Nat.pow_pos (by decide))
  simp [evenParentAtDepth,hdiv]
  omega

theorem oddParentAtDepth_eq (x y a k n : Nat)
    (hsum : x+y+1=2^n*(2*a+6))
    (hcost : 2*k+a+7+3*n=x+2*y) :
    oddParentAtDepth x y n=(a,k) := by
  have hmul : x+y+1=2^(n+1)*(a+3) := by
    calc
      x+y+1=2^n*(2*a+6) := hsum
      _=2^n*(2*(a+3)) := by congr 1 <;> omega
      _=2^(n+1)*(a+3) := by rw [Nat.pow_succ]; ac_rfl
  have hdiv : (x+y+1)/2^(n+1)=a+3 := by
    rw [hmul]
    exact Nat.mul_div_cancel_left (a+3) (Nat.pow_pos (by decide))
  simp [oddParentAtDepth,hdiv]
  omega

/-- A compact complete candidate list for all even-first high-input
parents of a target. It contains at most floor(V/2) entries. -/
def evenHighCandidates (x y v : Nat) : List (Nat × Nat) :=
  (evenDepthCandidates v x).map (fun n => evenParentAtDepth x y n)

/-- A compact complete candidate list for all odd-first high-input
parents of a target. It contains at most floor(V/2) entries. -/
def oddHighCandidates (x y v : Nat) : List (Nat × Nat) :=
  (oddDepthCandidates v x).map (fun n => oddParentAtDepth x y n)

theorem evenHighCandidates_length (x y v : Nat) :
    (evenHighCandidates x y v).length≤v/2 := by
  rw [evenHighCandidates,List.length_map]
  exact evenDepthCandidates_length v x

theorem oddHighCandidates_length (x y v : Nat) :
    (oddHighCandidates x y v).length≤v/2 := by
  rw [oddHighCandidates,List.length_map]
  exact oddDepthCandidates_length v x

/-- The exhaustive original-source inverse grammar yields the two
arithmetic equations for every even-first high predecessor. -/
theorem even_high_parent_equations (a k x y : Nat)
    (ha : 2≤a) (hk : 0<k) (hreg : a<2*k) (heven : a%2=0)
    (hy : 5≤y) (hedge : secNext (a,k)=some (x,y)) :
    ∃ n, x+y=2^n*(2*a+4) ∧ 2*k+a+7+3*n=x+2*y := by
  have hi := (section_preimage_all_iff a k x y).mp hedge
  have ha0 : a≠0 := by omega
  have ha1 : a≠1 := by omega
  have hk0 : k≠0 := by omega
  have hlow : ¬2*k≤a := by omega
  simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
    if_neg hk0,if_neg hlow,if_pos heven] at hi
  rcases hi with ⟨_,n,hs,hc⟩
  refine ⟨n,?_,?_⟩
  · have hbase : 2*(a-1)+6=2*a+4 := by omega
    rw [hbase] at hs
    exact hs
  · omega

/-- The exhaustive original-source inverse grammar yields the two
arithmetic equations for every odd-first high predecessor. -/
theorem odd_high_parent_equations (a k x y : Nat)
    (ha : 3≤a) (hk : 0<k) (hreg : a<2*k) (hodd : a%2=1)
    (hy : 5≤y) (hedge : secNext (a,k)=some (x,y)) :
    ∃ n, x+y+1=2^n*(2*a+6) ∧ 2*k+a+7+3*n=x+2*y := by
  have hi := (section_preimage_all_iff a k x y).mp hedge
  have ha0 : a≠0 := by omega
  have ha1 : a≠1 := by omega
  have hk0 : k≠0 := by omega
  have hlow : ¬2*k≤a := by omega
  have hnotEven : a%2≠0 := by omega
  simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
    if_neg hk0,if_neg hlow,if_neg hnotEven] at hi
  rcases hi with ⟨hy3,_⟩ | ⟨_,n,hs,hc⟩
  · omega
  · refine ⟨n,?_,?_⟩
    · have hbase : 2*(a-1)+8=2*a+6 := by omega
      rw [hbase] at hs
      exact hs
    · omega

/-- Every genuine even-first high predecessor is in the compact
valuation-indexed candidate list. -/
theorem even_high_parent_mem_candidates (a k x y v u : Nat)
    (ha : 2≤a) (hk : 0<k) (hreg : a<2*k) (heven : a%2=0)
    (hy : 5≤y) (hfact : x+y=2^v*(2*u+1))
    (hedge : secNext (a,k)=some (x,y)) :
    (a,k)∈evenHighCandidates x y v := by
  obtain ⟨n,hsum,hcost⟩ :=
    even_high_parent_equations a k x y ha hk hreg heven hy hedge
  have hfactor : 2^n*(2*a+4)=2^v*(2*u+1) :=
    hsum.symm.trans hfact
  have hbound := even_input_depth_val a n v u heven hfactor
  have hpar := even_input_depth_parity a k x y n heven hcost
  have hmem := evenDepthCandidates_mem v x n hbound hpar
  unfold evenHighCandidates
  apply List.mem_map.mpr
  exact ⟨n,hmem,evenParentAtDepth_eq x y a k n hsum hcost⟩

/-- Every genuine odd-first high predecessor is in the compact
valuation-indexed candidate list. -/
theorem odd_high_parent_mem_candidates (a k x y v u : Nat)
    (ha : 3≤a) (hk : 0<k) (hreg : a<2*k) (hodd : a%2=1)
    (hy : 5≤y) (hfact : x+y+1=2^v*(2*u+1))
    (hedge : secNext (a,k)=some (x,y)) :
    (a,k)∈oddHighCandidates x y v := by
  obtain ⟨n,hsum,hcost⟩ :=
    odd_high_parent_equations a k x y ha hk hreg hodd hy hedge
  have hfactor : 2^n*(2*a+6)=2^v*(2*u+1) :=
    hsum.symm.trans hfact
  have hbound := odd_input_depth_val a n v u hodd hfactor
  have hpar := odd_input_depth_parity a k x y n hodd hcost
  have hmem := oddDepthCandidates_mem v x n hbound hpar
  unfold oddHighCandidates
  apply List.mem_map.mpr
  exact ⟨n,hmem,oddParentAtDepth_eq x y a k n hsum hcost⟩

/-- Filtering by the unchanged original source turns the bounded
candidate list into an exact list of even-first high parents. -/
def evenHighExactCandidates (x y v : Nat) : List (Nat × Nat) :=
  (evenHighCandidates x y v).filter (fun p => decide (secNext p=some (x,y)))

/-- Filtering by the unchanged original source turns the bounded
candidate list into an exact list of odd-first high parents. -/
def oddHighExactCandidates (x y v : Nat) : List (Nat × Nat) :=
  (oddHighCandidates x y v).filter (fun p => decide (secNext p=some (x,y)))

theorem evenHighExactCandidates_length (x y v : Nat) :
    (evenHighExactCandidates x y v).length≤v/2 := by
  unfold evenHighExactCandidates
  exact Nat.le_trans (List.length_filter_le _ _) (evenHighCandidates_length x y v)

theorem oddHighExactCandidates_length (x y v : Nat) :
    (oddHighExactCandidates x y v).length≤v/2 := by
  unfold oddHighExactCandidates
  exact Nat.le_trans (List.length_filter_le _ _) (oddHighCandidates_length x y v)

theorem even_high_parent_mem_exact_candidates (a k x y v u : Nat)
    (ha : 2≤a) (hk : 0<k) (hreg : a<2*k) (heven : a%2=0)
    (hy : 5≤y) (hfact : x+y=2^v*(2*u+1))
    (hedge : secNext (a,k)=some (x,y)) :
    (a,k)∈evenHighExactCandidates x y v := by
  apply List.mem_filter.mpr
  exact ⟨even_high_parent_mem_candidates a k x y v u ha hk hreg heven hy hfact hedge,
    by simp [hedge]⟩

theorem odd_high_parent_mem_exact_candidates (a k x y v u : Nat)
    (ha : 3≤a) (hk : 0<k) (hreg : a<2*k) (hodd : a%2=1)
    (hy : 5≤y) (hfact : x+y+1=2^v*(2*u+1))
    (hedge : secNext (a,k)=some (x,y)) :
    (a,k)∈oddHighExactCandidates x y v := by
  apply List.mem_filter.mpr
  exact ⟨odd_high_parent_mem_candidates a k x y v u ha hk hreg hodd hy hfact hedge,
    by simp [hedge]⟩

#print axioms even_high_parent_equations
#print axioms odd_high_parent_equations
#print axioms even_high_parent_mem_exact_candidates
#print axioms odd_high_parent_mem_exact_candidates
#print axioms evenHighExactCandidates_length
#print axioms oddHighExactCandidates_length

end BB6.Agent34Valuation
