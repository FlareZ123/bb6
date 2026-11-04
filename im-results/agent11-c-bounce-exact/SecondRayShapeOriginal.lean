import FullSectionInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Ray
open BB6.Agent46

/-- Odd-sum positive section outputs have only odd-first-coordinate parents. -/
theorem odd_total_input_odd (a k x y : Nat) (hs : (x+y)%2=1)
    (h : sectionPreimageCriterion a k x y) : a%2=1 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageCriterion,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp only [sectionPreimageCriterion,if_pos ha0,if_neg hk0,if_pos hk1] at h
        omega
      · simp only [sectionPreimageCriterion,if_pos ha0,if_neg hk0,if_neg hk1] at h
        rcases h with ⟨n,heq,_⟩
        omega
  · by_cases ha1 : a=1
    · omega
    · by_cases hk0 : k=0
      · simp [sectionPreimageCriterion,ha0,ha1,hk0] at h
      · by_cases hdir : 2*k≤a
        · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,if_neg hk0,if_pos hdir] at h
          rcases h with ⟨hx,hy⟩
          omega
        · by_cases haEven : a%2=0
          · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hdir,if_pos haEven] at h
            obtain ⟨n,heq,_⟩ := h
            have hv : 2*(a-1)+6=2*(a+2) := by omega
            rw [hv] at heq
            have hev : 2^n*(2*(a+2))=2*(2^n*(a+2)) := by ac_rfl
            rw [hev] at heq
            omega
          · omega

def rayD (m:Nat) := 4^(m+1)*(3*m+4)
def rayX (m:Nat) := 6*m+5
def rayY (m:Nat) := rayD m-(6*m+6)

theorem rayFacts (m:Nat) :
  10≤rayY m ∧
  rayY m+6*m+6=rayD m ∧
  rayX m+rayY m+1=rayD m ∧
  (rayX m+rayY m)%2=1 ∧
  (rayX m+2*rayY m)%2=1 := by
  have hp : 1≤4^m := Nat.one_le_pow m 4 (by decide)
  have hmul : 3*m+4≤4^m*(3*m+4) := by
    simpa using Nat.mul_le_mul_right (3*m+4) hp
  have he : rayD m=4*(4^m*(3*m+4)) := by
    unfold rayD
    rw [Nat.pow_succ]
    ac_rfl
  have hbig : 12*m+16≤rayD m := by omega
  have hsub : rayY m+6*m+6=rayD m := by
    unfold rayY
    omega
  have hX : rayX m=6*m+5 := rfl
  have hpar : (rayD m)%2=0 := by
    rw [he]
    omega
  constructor
  · omega
  constructor
  · exact hsub
  constructor
  · omega
  constructor
  · omega
  · omega

theorem ray_source_odd (m a k:Nat)
    (h: sectionPreimageCriterion a k (rayX m) (rayY m)) : a%2=1 :=
  odd_total_input_odd a k (rayX m) (rayY m) (rayFacts m).2.2.2.1 h

/-- In the high bounce sector, the depth is always odd. -/
theorem ray_high_shape (m a k :Nat)
  (ha: 2≤a) (hk:0<k) (hr: a<2*k)
  (h: sectionPreimageCriterion a k (rayX m) (rayY m)) :
  ∃ n : Nat, n%2=1 ∧
    rayD m=2^(n+1)*(a+3) ∧
    2*k+a+7+3*n=rayX m+2*rayY m := by
  have hodd:=ray_source_odd m a k h
  have h0:a≠0 := by omega
  have h1:a≠1 := by omega
  have hk0:k≠0 := by omega
  have hdir: ¬(2*k≤a) := by omega
  have heven:¬a%2=0 := by omega
  simp only [sectionPreimageCriterion,if_neg h0,if_neg h1,if_neg hk0,if_neg hdir,if_neg heven] at h
  obtain ⟨n,hs,hc⟩ := h
  have hA:a-1+1=a := by omega
  have hfactor:2*(a-1)+8=2*(a+3) := by omega
  rw [hfactor] at hs hc
  have hsum:rayX m+rayY m+1=rayD m := (rayFacts m).2.2.1
  have he : 2^n*(2*(a+3))=2^(n+1)*(a+3) := by
    rw [Nat.pow_succ]
    ac_rfl
  rw [he] at hs
  refine ⟨n,?_,?_,?_⟩
  · have ho : (rayX m+2*rayY m)%2=1 := (rayFacts m).2.2.2.2
    omega
  · omega
  · omega

/-- Exhaustive necessary source-parent classes for the second-stopping ray. -/
theorem ray_parent_necessary (m a k : Nat)
  (h : sectionPreimageCriterion a k (rayX m) (rayY m)) :
  (a+3=rayD m ∧ 2*k+2=rayY m) ∨
  (a=1 ∧ 4≤k ∧ ∃ n:Nat,
     rayD m=2^n*16 ∧
     2*k+11+3*n=rayX m+2*rayY m) ∨
  (3≤a ∧ a<2*k ∧ ∃ n:Nat, n%2=1 ∧
     rayD m=2^(n+1)*(a+3) ∧
     2*k+a+7+3*n=rayX m+2*rayY m) := by
  have hodd := ray_source_odd m a k h
  have hf := rayFacts m
  by_cases ha0 : a=0
  · omega
  by_cases ha1 : a=1
  · by_cases hk0 : k=0
    · simp [sectionPreimageCriterion,ha0,ha1,hk0] at h
    by_cases hk1 : k=1
    · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1] at h
    by_cases hk2 : k=2
    · simp only [sectionPreimageCriterion,if_neg ha0,if_pos ha1,
        if_neg hk0,if_neg hk1,if_pos hk2] at h
      omega
    by_cases hk3 : k=3
    · simp only [sectionPreimageCriterion,if_neg ha0,if_pos ha1,
        if_neg hk0,if_neg hk1,if_neg hk2,if_pos hk3] at h
      omega
    simp only [sectionPreimageCriterion,if_neg ha0,if_pos ha1,
      if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at h
    rcases h with ⟨n,hs,hc⟩
    right
    left
    refine ⟨ha1,by omega,⟨n,?_,?_⟩⟩
    · omega
    · omega
  · have ha2 : 2≤a := by omega
    by_cases hk0 : k=0
    · simp [sectionPreimageCriterion,ha0,ha1,hk0] at h
    by_cases hdir : 2*k≤a
    · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,
       if_neg hk0,if_pos hdir] at h
      rcases h with ⟨hx,hy⟩
      left
      constructor
      · omega
      · omega
    · have hh := ray_high_shape m a k ha2 (by omega) (by omega) h
      right
      right
      exact ⟨by omega,by omega,hh⟩

theorem ray_parent_sufficient (m a k : Nat) :
  ((a+3=rayD m ∧ 2*k+2=rayY m) ∨
  (a=1 ∧ 4≤k ∧ ∃ n:Nat,
     rayD m=2^n*16 ∧
     2*k+11+3*n=rayX m+2*rayY m) ∨
  (3≤a ∧ a<2*k ∧ ∃ n:Nat, n%2=1 ∧
     rayD m=2^(n+1)*(a+3) ∧
     2*k+a+7+3*n=rayX m+2*rayY m)) →
  sectionPreimageCriterion a k (rayX m) (rayY m) := by
  intro h
  have hf:=rayFacts m
  rcases h with ⟨hD,hK⟩ | ⟨ha,hk,n,hD,hK⟩ | ⟨ha,hk,n,hn,hD,hK⟩
  · have ha0:a≠0:=by omega
    have ha1:a≠1:=by omega
    have hk0:k≠0:=by omega
    have hreg:2*k≤a:=by omega
    simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,
      if_neg hk0,if_pos hreg]
    constructor
    · omega
    · omega
  · have ha0:a≠0:=by omega
    have hk0:k≠0:=by omega
    have hk1:k≠1:=by omega
    have hk2:k≠2:=by omega
    have hk3:k≠3:=by omega
    simp only [sectionPreimageCriterion,if_neg ha0,if_pos ha,
      if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3]
    refine ⟨n,?_,?_⟩
    · omega
    · omega
  · have ha0:a≠0:=by omega
    have ha1:a≠1:=by omega
    have hk0:k≠0:=by omega
    have hreg:¬2*k≤a:=by omega
    have haOdd:a%2=1:=by
      have hh:(rayX m+2*rayY m)%2=1:=hf.2.2.2.2
      omega
    have heven:¬a%2=0:=by omega
    simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,
      if_neg hk0,if_neg hreg,if_neg heven]
    refine ⟨n,?_,?_⟩
    · have hfactor : 2*(a-1)+8=2*(a+3):=by omega
      rw [hfactor]
      have hpow : 2^n*(2*(a+3))=2^(n+1)*(a+3):=by rw [Nat.pow_succ];ac_rfl
      rw [hpow]
      omega
    · omega

theorem ray_parent_iff (m a k : Nat) :
  sectionPreimageCriterion a k (rayX m) (rayY m) ↔
  (a+3=rayD m ∧ 2*k+2=rayY m) ∨
  (a=1 ∧ 4≤k ∧ ∃ n:Nat,
     rayD m=2^n*16 ∧
     2*k+11+3*n=rayX m+2*rayY m) ∨
  (3≤a ∧ a<2*k ∧ ∃ n:Nat, n%2=1 ∧
     rayD m=2^(n+1)*(a+3) ∧
     2*k+a+7+3*n=rayX m+2*rayY m) := by
  constructor
  · exact ray_parent_necessary m a k
  · exact ray_parent_sufficient m a k

/-- Exact source-connected theorem; all possible input sectors are covered.
    It neither asserts rooted reachability nor determines Machine C halting. -/
theorem original_ray_parent_iff (m a k : Nat) :
  secNext (a,k) = some (rayX m, rayY m) ↔
  (a+3=rayD m ∧ 2*k+2=rayY m) ∨
  (a=1 ∧ 4≤k ∧ ∃ n:Nat,
     rayD m=2^n*16 ∧
     2*k+11+3*n=rayX m+2*rayY m) ∨
  (3≤a ∧ a<2*k ∧ ∃ n:Nat, n%2=1 ∧
     rayD m=2^(n+1)*(a+3) ∧
     2*k+a+7+3*n=rayX m+2*rayY m) := by
  have hy : 5≤rayY m := by
    have hf := rayFacts m
    omega
  exact (complete_section_inverse a k (rayX m) (rayY m) hy).trans
    (ray_parent_iff m a k)

#print axioms original_ray_parent_iff
#print axioms ray_parent_iff
#print axioms ray_high_shape
end BB6.Agent11Ray
