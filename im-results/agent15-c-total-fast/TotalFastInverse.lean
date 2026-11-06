import SectionFastInverseOriginal
import SectionAllInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15TotalFast
open BB6.Agent46 BB6.Agent11Fast

/-- Additional inverse candidates for the exceptional even-bounce y=3 branch. -/
def threeOne (x n : Nat) : List (Nat × Nat) :=
  let a := (x+6)/2^(n+1)-3
  [(1,(x-3-3*n)/2), (a,(x+1-a-3*n)/2)]

def threeUnfiltered (x : Nat) : List (Nat × Nat) :=
  (List.range (Nat.log2 (x+6)+1)).flatMap (threeOne x)

/-- A uniform logarithmic-sized candidate list for every target, including small y. -/
def totalFastUnfiltered (x y : Nat) : List (Nat × Nat) :=
  fastUnfiltered x y ++ [(0,1), (1,0), (1,1)] ++ threeUnfiltered x

def totalFastCandidates (x y : Nat) : List (Nat × Nat) :=
  (totalFastUnfiltered x y).filter (fun p => secNext p=some (x,y))

theorem threeUnfiltered_length (x : Nat) :
    (threeUnfiltered x).length = 2*(Nat.log2 (x+6)+1) := by
  have h : ∀ l : List Nat, (l.map (fun _ => 2)).sum = 2*l.length := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp [ih]; omega
  simp [threeUnfiltered,List.length_flatMap, threeOne,h]

theorem totalFastUnfiltered_length (x y : Nat) :
    (totalFastUnfiltered x y).length =
      4*fastCap x y+7+2*(Nat.log2 (x+6)+1) := by
  simp only [totalFastUnfiltered,List.length_append,fastUnfiltered_length,
    threeUnfiltered_length,List.length_cons,List.length_nil]

private theorem mem_fast (x y a k : Nat)
    (h : (a,k)∈fastUnfiltered x y) :
    (a,k)∈totalFastUnfiltered x y := by
  unfold totalFastUnfiltered
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h)))

private theorem mem_small (x y a k : Nat)
    (h : (a,k)∈[(0,1),(1,0),(1,1)]) :
    (a,k)∈totalFastUnfiltered x y := by
  unfold totalFastUnfiltered
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))

private theorem mem_three (x y n a k : Nat)
    (hn : n<Nat.log2 (x+6)+1)
    (h : (a,k)∈threeOne x n) :
    (a,k)∈totalFastUnfiltered x y := by
  unfold totalFastUnfiltered
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  exact ⟨n,List.mem_range.mpr hn,h⟩

private theorem log_depth (x n b : Nat)
    (hb:0<b) (he:x+6=2^n*b) :
    n<Nat.log2 (x+6)+1 := by
  have hp:x+6≠0 := by omega
  have hpow:2^n≤x+6 := by
    rw [he]
    exact Nat.le_mul_of_pos_right (2^n) hb
  have hle:= (Nat.le_log2 hp).mpr hpow
  omega

private theorem three_one_present (x k n:Nat)
    (hk:4≤k) (hs:x+6=2^n*16)
    (hc:(2*k-3)+16+3*n=x+10) :
    (1,k) ∈ totalFastUnfiltered x 3 := by
  have hn := log_depth x n 16 (by decide) hs
  have hk' : (x-3-3*n)/2=k := by omega
  apply mem_three x 3 n 1 k hn
  simp [threeOne,hk']

private theorem three_odd_present (x a k n : Nat)
    (ha:3≤a) (hk:0<k) (hreg:a<2*k)
    (hs:x+6=2^n*(2*(a-1)+8))
    (hc:(2*k-a+3)+(2*(a-1)+8)+3*n=x+10) :
    (a,k)∈totalFastUnfiltered x 3 := by
  have hpositive : 0<2*(a-1)+8 := by omega
  have hn := log_depth x n (2*(a-1)+8) hpositive hs
  have hp : x+6=2^(n+1)*(a+3) := by
    calc
      x+6=2^n*(2*(a-1)+8) := hs
      _=2^n*(2*(a+3)) := by congr 1 <;> omega
      _=2^(n+1)*(a+3) := by rw [Nat.pow_succ]; ac_rfl
  have ha' : (x+6)/2^(n+1)-3=a := by
    rw [hp,Nat.mul_div_cancel_left (a+3) (Nat.pow_pos (by decide))]
    omega
  have hk' : (x+1-((x+6)/2^(n+1)-3)-3*n)/2=k := by
    rw [ha']
    omega
  apply mem_three x 3 n a k hn
  simp only [threeOne, List.mem_cons, List.mem_singleton, Prod.mk.injEq]
  right
  left
  exact ⟨ha'.symm,hk'.symm⟩

private theorem total_unfiltered_complete (a k x y:Nat)
    (h:secNext (a,k)=some (x,y)) :
    (a,k)∈totalFastUnfiltered x y := by
  by_cases hy:5≤y
  · exact mem_fast x y a k (fastUnfiltered_complete a k x y hy h)
  have hi := (section_preimage_all_iff a k x y).mp h
  by_cases ha0:a=0
  · by_cases hk0:k=0
    · simp [sectionPreimageAll,ha0,hk0] at hi
    · by_cases hk1:k=1
      · have hp : (a,k)=(0,1) := by simp [ha0,hk1]
        rw [hp]
        exact mem_small x y 0 1 (by simp)
      · simp only [sectionPreimageAll, if_pos ha0,if_neg hk0,if_neg hk1] at hi
        rcases hi with ⟨hy4,n,hs,hc⟩
        have hk2:2≤k := by omega
        exact mem_fast x y a k (by
          subst a
          apply zero_depth_present x y k n hk2 hs
          omega)
  · by_cases ha1:a=1
    · by_cases hk0:k=0
      · have hp : (a,k)=(1,0) := by simp [ha1,hk0]
        rw [hp]
        exact mem_small x y 1 0 (by simp)
      · by_cases hk1:k=1
        · have hp : (a,k)=(1,1) := by simp [ha1,hk1]
          rw [hp]
          exact mem_small x y 1 1 (by simp)
        · by_cases hk2:k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hi
            omega
          · by_cases hk3:k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hi
              omega
            · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at hi
              rcases hi with ⟨h3,n,hs,hc⟩ | ⟨h5,_⟩
              · subst y
                have hk4:4≤k := by omega
                subst a
                exact three_one_present x k n hk4 hs hc
              · omega
    · have ha2:2≤a := by omega
      by_cases hk0:k=0
      · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,if_pos hk0] at hi
        rcases hi with ⟨hx,hy2⟩
        have hxa : a=x+2 := by omega
        subst a
        subst k
        exact mem_fast x y (x+2) 0 (by simp [fastUnfiltered])
      · by_cases hreg:2*k≤a
        · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
            if_neg hk0,if_pos hreg] at hi
          rcases hi with ⟨hx,hy2⟩
          have he:a=x+y-2 := by omega
          have hk':k=(y-2)/2 := by omega
          exact mem_fast x y a k (direct_present x y a k he hk')
        · by_cases haEven:a%2=0
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hreg,if_pos haEven] at hi
            rcases hi with ⟨hy4,n,hs,hc⟩
            exact mem_fast x y a k (even_depth_present x y a k n ha2 (by omega) (by omega) hs hc)
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hreg,if_neg haEven] at hi
            rcases hi with ⟨h3,n,hs,hc⟩ | ⟨h5,_⟩
            · subst y
              exact three_odd_present x a k n (by omega) (by omega) (by omega) hs hc
            · omega

/-- Genuine original-source completeness of the logarithmic inverse list for ALL targets. -/
theorem totalFastCandidates_exact (a k x y:Nat) :
    (a,k)∈totalFastCandidates x y ↔ secNext (a,k)=some (x,y) := by
  simp only [totalFastCandidates,List.mem_filter,decide_eq_true_eq]
  constructor
  · intro hh; exact hh.2
  · intro hh; exact ⟨total_unfiltered_complete a k x y hh,hh⟩

#print axioms totalFastCandidates_exact
#print axioms totalFastUnfiltered_length
end BB6.Agent15TotalFast
