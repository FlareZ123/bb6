import SecondRayOddReach
import Std
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Ray
open BB6.Agent46

def rayDepthBound (m:Nat) := Nat.log2 (rayD m)+1

def rayOne (m n:Nat) : Nat×Nat :=
  (1,(rayX m+2*rayY m-(11+3*n))/2)

def rayHigh (m n:Nat) : Nat×Nat :=
  let A:=rayD m / 2^(n+1)
  (A-3,(rayX m+2*rayY m-(A+4+3*n))/2)

def rayRawCandidates (m:Nat) : List (Nat×Nat) :=
  (oddRayDirect m :: (List.range (rayDepthBound m)).map (rayOne m)) ++
    (List.range (rayDepthBound m)).map (rayHigh m)

def rayAllParents (m:Nat) : List (Nat×Nat) :=
  (rayRawCandidates m).filter (fun p => decide (secNext p=some (rayX m,rayY m)))

theorem rayDepthBound_of_pow (m n:Nat)
    (hp:2^n≤rayD m) : n<rayDepthBound m := by
  have hf:=rayFacts m
  have hD: rayD m≠0 := by omega
  exact Nat.lt_succ_of_le ((Nat.le_log2 hD).mpr hp)

theorem rayRawCandidates_complete (m a k:Nat)
    (h:secNext (a,k)=some (rayX m,rayY m)) :
    (a,k)∈rayRawCandidates m := by
  have hi:=(original_ray_parent_iff m a k).mp h
  simp only [rayRawCandidates,List.mem_append,List.mem_cons,List.mem_map,List.mem_range]
  rcases hi with hd | he | hh
  · exact Or.inl (Or.inl ((oddRayDirect_iff m a k).mpr hd))
  · obtain ⟨ha,hk,n,hpow,hcost⟩ := he
    have hle : 2^n≤rayD m := by
      have hbound : 2^n ≤ 2^n*16 := by omega
      omega
    have hn : n<rayDepthBound m := rayDepthBound_of_pow m n hle
    have hk' : k=(rayX m+2*rayY m-(11+3*n))/2 := by omega
    left
    right
    exact ⟨n,hn,by simp [rayOne,ha,hk']⟩
  · obtain ⟨ha,hhigh,n,hnodd,hpow,hcost⟩ := hh
    have hp : 0<2^(n+1) := Nat.pow_pos (by decide)
    have hle : 2^n≤rayD m := by
      have h2 : 2^n≤2^(n+1) := Nat.pow_le_pow_right (by decide) (by omega)
      have h3 : 2^(n+1)≤2^(n+1)*(a+3) := by
        apply Nat.le_mul_of_pos_right
        omega
      omega
    have hn:n<rayDepthBound m := rayDepthBound_of_pow m n hle
    have hdiv : rayD m / 2^(n+1)=a+3 := by
      rw [hpow]
      exact Nat.mul_div_cancel_left (a+3) hp
    have hk' : k=(rayX m+2*rayY m-((a+3)+4+3*n))/2 := by omega
    right
    refine ⟨n,hn,?_⟩
    dsimp [rayHigh]
    rw [hdiv]
    have ha' : a+3-3=a := by omega
    rw [ha',←hk']

theorem rayAllParents_exact (m a k:Nat) :
    (a,k)∈rayAllParents m ↔ secNext (a,k)=some (rayX m,rayY m) := by
  rw [rayAllParents,List.mem_filter]
  constructor
  · intro h
    exact of_decide_eq_true h.2
  · intro h
    exact ⟨rayRawCandidates_complete m a k h, by simpa only [decide_eq_true_eq] using h⟩

theorem rayRawCandidates_length (m:Nat) :
    (rayRawCandidates m).length=2*rayDepthBound m+1 := by
  simp only [rayRawCandidates,List.length_append,List.length_cons,List.length_map,List.length_range]
  omega

/-- Uniform logarithmic-in-target-size upper bound on all source candidate
    entries, covering even and odd stopping indices without valuation cases. -/
theorem rayAllParents_length_le (m:Nat) :
  (rayAllParents m).length ≤ 2*Nat.log2 (rayD m)+3 := by
  have hle := List.length_filter_le
    (fun p:Nat×Nat => decide (secNext p=some (rayX m,rayY m)))
    (rayRawCandidates m)
  have hlen := rayRawCandidates_length m
  dsimp [rayAllParents,rayDepthBound] at *
  omega

/-- Source-exact finite reduction of genuine blank-origin stopping reachability
    for EVERY parameter m. At most 2*log2(D)+3 possible parents are tested. -/
theorem all_ray_root_reduction (m:Nat) :
  RayReach (rayX m,rayY m) ↔
    ∃ p:Nat×Nat, p∈rayAllParents m ∧ RayReach p := by
  have hnot : (rayX m,rayY m)≠(5,1) := by
    intro h
    have he:rayY m=1 := (Prod.mk.inj h).2
    have hh := (rayFacts m).1
    omega
  rw [ray_reach_predecessor _ hnot]
  constructor
  · rintro ⟨⟨a,k⟩,hr,he⟩
    exact ⟨(a,k),(rayAllParents_exact m a k).mpr he,hr⟩
  · rintro ⟨⟨a,k⟩,hin,hr⟩
    exact ⟨(a,k),hr,(rayAllParents_exact m a k).mp hin⟩

#print axioms rayAllParents_exact
#print axioms all_ray_root_reduction
#print axioms rayRawCandidates_length
end BB6.Agent11Ray
