import PurePowerFan
import Lean.Elab.Tactic.Omega

namespace BB6.Agent12ValuationParents
open BB6.Agent12PureFan

def rounded (x y : Nat) := x+y+(x+y)%2
def v2 (q : Nat) : Nat := (q:Int).trailingZeros

private theorem factor_v2 (q n c : Nat) (hc : c>0) (he : q=2^n*c) : n≤v2 q := by
  have h : (q:Int)=(c:Int) <<< n := by
    rw [Int.shiftLeft_eq',he,Int.natCast_mul,Int.mul_comm]
  unfold v2
  rw [h,Int.trailingZeros_shiftLeft (by omega : (c:Int)≠0)]
  omega

private theorem even_pow (n : Nat) (hn : 1≤n) : 2^n%2=0 :=
  Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 hn)

/-- One possible high-left parent for each depth, with its exact region and
    arithmetic equalities checked. No source transition is simulated. -/
def regularAt (x y n : Nat) : Option (Nat × Nat) :=
  let o := (x+y)%2
  let a := rounded x y / 2^(n+1)-2-o
  let k := (x+2*y-a-7-3*n)/2
  if 2≤a ∧ a<2*k ∧ a%2=o ∧ rounded x y=2^(n+1)*(a+2+o) ∧
      2*k+a+7+3*n=x+2*y then some (a,k) else none

def directAt (x y : Nat) : Option (Nat × Nat) :=
  if y%2=0 ∧ 2≤y then some (x+y-2,(y-2)/2) else none

def zeroAt (x y : Nat) : Option (Nat × Nat) :=
  let v := v2 (rounded x y)
  let k := (x+2*y-3*v)/2
  if (x+y)%2=0 ∧ 3≤v ∧ rounded x y=2^v ∧ 2≤k ∧ 2*k+3*v=x+2*y
    then some (0,k) else none

def oneAt (x y : Nat) : Option (Nat × Nat) :=
  let v := v2 (rounded x y)
  let k := (x+2*y+1-3*v)/2
  if (x+y)%2=1 ∧ 4≤v ∧ rounded x y=2^v ∧ 4≤k ∧ 2*k+3*v=x+2*y+1
    then some (1,k) else none

/-- The ordinary candidate list is bounded by the two-adic valuation, not
    the bit length of the counters. Includes the two exceptional parents. -/
def valuationParents (x y : Nat) : List (Nat × Nat) :=
  ([directAt x y,zeroAt x y,oneAt x y].filterMap id) ++
    (List.range (v2 (rounded x y))).filterMap (regularAt x y)

private theorem pure_v2 (n : Nat) : v2 (2^n)=n := by
  have h : ((2^n:Nat):Int)=(1:Int) <<< n := by simp [Int.shiftLeft_eq']
  unfold v2
  rw [h, Int.trailingZeros_shiftLeft (by decide : (1:Int)≠0)]
  have h1 : (1:Int).trailingZeros=0 := by decide
  omega

private theorem regular_sound (a k x y n : Nat)
    (h : regularAt x y n=some (a,k)) : RawParent a k x y := by
  simp only [regularAt] at h
  split at h
  next hcond =>
    simp only [Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨ha,hk⟩ := h
    rw [ha] at hk
    rw [ha,hk] at hcond
    obtain ⟨ha2,hreg,hpar,hs,hw⟩ := hcond
    by_cases ho : (x+y)%2=0
    · have he : x+y=2^(n+1)*(a+2) := by simpa [rounded,ho] using hs
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ha2,hreg,by omega,n,he,hw⟩)))
    · have h1 : (x+y)%2=1 := by omega
      have he : x+y+1=2^(n+1)*(a+3) := by simpa [rounded,h1,Nat.add_assoc] using hs
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ha2,hreg,by omega,n,he,hw⟩)))
  next => contradiction

private theorem regular_complete (a k x y n : Nat) (ha : 2≤a) (hk : a<2*k)
    (hp : a%2=(x+y)%2) (hs : rounded x y=2^(n+1)*(a+2+(x+y)%2))
    (hw : 2*k+a+7+3*n=x+2*y) : (a,k)∈valuationParents x y := by
  have hv := factor_v2 (rounded x y) (n+1) (a+2+(x+y)%2) (by omega) hs
  have ha' : rounded x y / 2^(n+1)-2-(x+y)%2=a := by
    rw [hs,Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide))]
    omega
  have hk' : (x+2*y-a-7-3*n)/2=k := by omega
  apply List.mem_append.mpr
  right
  apply List.mem_filterMap.mpr
  refine ⟨n,List.mem_range.mpr (by omega),?_⟩
  simp only [regularAt]
  rw [ha',hk']
  simp [ha,hk,hp,hs,hw]

/-- High-right inverse list is exactly the complete arithmetic grammar. -/
theorem valuationParents_exact (a k x y : Nat) (hy : 8≤y) :
    (a,k)∈valuationParents x y ↔ RawParent a k x y := by
  constructor
  · intro h
    rcases List.mem_append.mp h with h|h
    · obtain ⟨p,hp,he⟩ := List.mem_filterMap.mp h
      change p=some (a,k) at he
      subst p
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with hp|hp|hp
      · unfold directAt at hp
        split at hp
        next h =>
          simp only [Option.some.injEq,Prod.mk.injEq] at hp
          exact Or.inl ⟨h.1,by omega,by omega⟩
        next => contradiction
      · simp only [zeroAt] at hp
        split at hp
        next h =>
          simp only [Option.some.injEq,Prod.mk.injEq] at hp
          let v := v2 (rounded x y)
          have hs : x+y=2^(v-3)*8 := by
            have he : 2^v=2^(v-3)*8 := by
              rw [←show 2^3=8 by decide,←Nat.pow_add,show v-3+3=v by omega]
            rw [←he,←h.2.2.1]
            simp [rounded,h.1]
          exact Or.inr (Or.inl ⟨by omega,by omega,v-3,hs,by omega⟩)
        next => contradiction
      · simp only [oneAt] at hp
        split at hp
        next h =>
          simp only [Option.some.injEq,Prod.mk.injEq] at hp
          let v := v2 (rounded x y)
          have hs : x+y+1=2^(v-4)*16 := by
            have he : 2^v=2^(v-4)*16 := by
              rw [←show 2^4=16 by decide,←Nat.pow_add,show v-4+4=v by omega]
            rw [←he,←h.2.2.1]
            simp [rounded,h.1]
          exact Or.inr (Or.inr (Or.inl ⟨by omega,by omega,v-4,hs,by omega⟩))
        next => contradiction
    · obtain ⟨n,_,he⟩ := List.mem_filterMap.mp h
      exact regular_sound a k x y n he
  · intro h
    rcases h with h|h|h|h|h
    · obtain ⟨he,ha,hk⟩ := h
      apply List.mem_append.mpr
      left
      apply List.mem_filterMap.mpr
      exact ⟨directAt x y,by simp,by simp [directAt,he,show 2≤y by omega,show x+y-2=a by omega,show (y-2)/2=k by omega]⟩
    · obtain ⟨rfl,hk,n,hs,hw⟩ := h
      have hs' : x+y=2^(n+3) := by rw [Nat.pow_add]; exact hs
      have hp := even_pow (n+3) (by omega)
      have ho : (x+y)%2=0 := by omega
      have hq : rounded x y=2^(n+3) := by simp [rounded,ho,hs']
      have hv : v2 (rounded x y)=n+3 := by rw [hq,pure_v2]
      have hk' : (x+2*y-3*(n+3))/2=k := by omega
      apply List.mem_append.mpr
      left
      apply List.mem_filterMap.mpr
      refine ⟨zeroAt x y,by simp,?_⟩
      simp only [zeroAt]
      rw [hv,hk']
      simp [hq,ho,hk,show 2*k+3*(n+3)=x+2*y by omega]
    · obtain ⟨rfl,hk,n,hs,hw⟩ := h
      have hs' : x+y+1=2^(n+4) := by rw [Nat.pow_add]; exact hs
      have hp := even_pow (n+4) (by omega)
      have ho : (x+y)%2=1 := by omega
      have hq : rounded x y=2^(n+4) := by simp [rounded,ho,hs']
      have hv : v2 (rounded x y)=n+4 := by rw [hq,pure_v2]
      have hk' : (x+2*y+1-3*(n+4))/2=k := by omega
      apply List.mem_append.mpr
      left
      apply List.mem_filterMap.mpr
      refine ⟨oneAt x y,by simp,?_⟩
      simp only [oneAt]
      rw [hv,hk']
      simp [hq,ho,hk,show 2*k+3*(n+4)=x+2*y+1 by omega]
    · obtain ⟨ha,hreg,hp,n,hs,hw⟩ := h
      have h2 := even_pow (n+1) (by omega)
      have hmod := Nat.mul_mod (2^(n+1)) (a+2) 2
      rw [h2,Nat.zero_mul,Nat.zero_mod] at hmod
      have ho : (x+y)%2=0 := by omega
      apply regular_complete a k x y n ha hreg (by omega) ?_ hw
      simpa [rounded,ho] using hs
    · obtain ⟨ha,hreg,hp,n,hs,hw⟩ := h
      have h2 := even_pow (n+1) (by omega)
      have hmod := Nat.mul_mod (2^(n+1)) (a+3) 2
      rw [h2,Nat.zero_mul,Nat.zero_mod] at hmod
      have ho : (x+y)%2=1 := by omega
      apply regular_complete a k x y n ha hreg (by omega) ?_ hw
      simpa [rounded,ho,Nat.add_assoc] using hs

#print axioms valuationParents_exact
end BB6.Agent12ValuationParents
