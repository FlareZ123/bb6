import SlopeCycleAdapter
import ValuationEdges

namespace PeriodicMacro
open ValuationPacking
open FiniteCyclicValuation

def flipLetter (x : Letter) : Letter := ⟨x.j,!x.isE⟩
def flipWord (xs : List Letter) : List Letter := xs.map flipLetter

@[simp] theorem flipLetter_j (x : Letter) : (flipLetter x).j=x.j := rfl
@[simp] theorem flipLetter_scale (x : Letter) : scale (flipLetter x)=scale x := rfl

theorem M_flip (xs : List Letter) : M (flipWord xs)=M xs := by
  induction xs with
  | nil => simp [flipWord,M]
  | cons x xs ih =>
      change scale x * M (flipWord xs) = scale x * M xs
      rw [ih]

theorem A_flip (xs : List Letter) : A (flipWord xs)=A xs := by
  induction xs with
  | nil => simp [flipWord,A]
  | cons x xs ih =>
      change 1 + scale x * A (flipWord xs) = 1 + scale x * A xs
      rw [ih]

theorem J_flip (xs : List Letter) : J (flipWord xs)=J xs := by
  induction xs with
  | nil => simp [flipWord,J]
  | cons x xs ih =>
      change x.j + J (flipWord xs) = x.j + J xs
      rw [ih]

theorem T_append (xs ys : List Letter) : T (xs++ys)=T xs+T ys := by
  induction xs with
  | nil => simp [T]
  | cons x xs ih => simp [T,ih,Nat.add_assoc]

theorem J_append (xs ys : List Letter) : J (xs++ys)=J xs+J ys := by
  induction xs with
  | nil => simp [J]
  | cons x xs ih => simp [J,ih,Nat.add_assoc]

theorem rankCost_flip_sum (x : Letter) :
    rankCost x + rankCost (flipLetter x)=6*x.j+6 := by
  cases x with
  | mk j isE =>
      cases isE <;> simp [rankCost,flipLetter] <;> omega

theorem T_plus_flip (xs : List Letter) :
    T xs + T (flipWord xs)=6*(J xs+xs.length) := by
  induction xs with
  | nil => simp [T,J,flipWord]
  | cons x xs ih =>
      change (rankCost x + T xs) +
        (rankCost (flipLetter x) + T (flipWord xs)) =
        6*(x.j + J xs + (xs.length+1))
      have hc := rankCost_flip_sum x
      omega

theorem T_double_flip (xs : List Letter) :
    T (xs++flipWord xs)=6*(J xs+xs.length) := by
  rw [T_append]
  exact T_plus_flip xs

theorem slopeWalk_transfer {K : Nat} {xs : List Letter} {d f : Nat}
    (h : SlopeWalk K xs d f) : M xs*f=d+A xs*K := by
  induction h with
  | nil d => simp [M,A]
  | @cons x xs d e f head tail ih =>
      simp only [M,A]
      calc
        scale x*M xs*f = scale x*(M xs*f) := by ac_rfl
        _ = scale x*(e+A xs*K) := by rw [ih]
        _ = scale x*e + scale x*(A xs*K) := Nat.mul_add _ _ _
        _ = d+K + scale x*(A xs*K) := by rw [head]
        _ = d+(1+scale x*A xs)*K := by
          simp [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

theorem slopeWalk_append_inv {K : Nat} {xs ys : List Letter} {d f : Nat}
    (h : SlopeWalk K (xs++ys) d f) :
    ∃ m, SlopeWalk K xs d m ∧ SlopeWalk K ys m f := by
  induction xs generalizing d with
  | nil => exact ⟨d,SlopeWalk.nil d,by simpa using h⟩
  | cons x xs ih =>
      cases h with
      | @cons _ _ _ e _ head tail =>
          obtain ⟨m,h1,h2⟩ := ih tail
          exact ⟨m,SlopeWalk.cons head h1,h2⟩

theorem doubled_midpoint {K : Nat} {xs : List Letter} {d : Nat}
    (h : SlopeWalk K (xs++flipWord xs) d d) :
    ∃ m, SlopeWalk K xs d m ∧ SlopeWalk K (flipWord xs) m d ∧ m=d := by
  obtain ⟨m,h1,h2⟩ := slopeWalk_append_inv h
  have ht1 := slopeWalk_transfer h1
  have ht2 := slopeWalk_transfer h2
  rw [M_flip,A_flip] at ht2
  have hsum : M xs*m+m=M xs*d+d := by omega
  have hmul : (M xs+1)*m=(M xs+1)*d := by
    calc
      (M xs+1)*m = M xs*m+m := by simp [Nat.add_mul]
      _ = M xs*d+d := hsum
      _ = (M xs+1)*d := by simp [Nat.add_mul]
  have hmd : m=d := Nat.mul_left_cancel (by omega : 0<M xs+1) hmul
  exact ⟨m,h1,h2,hmd⟩

theorem halve_slopeWalk {K : Nat} {xs : List Letter} {d f : Nat}
    (h : SlopeWalk K xs d f)
    (hK : K%2=0) (hf : f%2=0)
    (hj : ∀ x : Letter, x∈xs → 0<x.j) :
    d%2=0 ∧ SlopeWalk (K/2) xs (d/2) (f/2) := by
  induction h with
  | nil d => exact ⟨hf,SlopeWalk.nil (d/2)⟩
  | @cons x xs d e f head tail ih =>
      have hxj : 0<x.j := hj x (by simp)
      have hjtail : ∀ y : Letter, y∈xs → 0<y.j := by
        intro y hy
        exact hj y (by simp [hy])
      have ht := ih hf hjtail
      have heven : e%2=0 := ht.1
      have he2 : e=2*(e/2) := by omega
      have hhead2 : 2*(scale x*(e/2))=d+K := by
        calc
          2*(scale x*(e/2)) = scale x*(2*(e/2)) := by ac_rfl
          _ = scale x*e := by rw [← he2]
          _ = d+K := head
      have hd : d%2=0 := by omega
      have heq : scale x*(e/2)=d/2+K/2 := by
        have hd2 : d=2*(d/2) := by omega
        have hk2 : K=2*(K/2) := by omega
        have hdouble : 2*(scale x*(e/2))=2*(d/2+K/2) := by
          calc
            2*(scale x*(e/2)) = d+K := hhead2
            _ = 2*(d/2+K/2) := by omega
        exact Nat.mul_left_cancel (by decide : 0<(2:Nat)) hdouble
      exact ⟨hd,SlopeWalk.cons heq ht.2⟩

private theorem scale_even2 (x : Letter) (hj : 0<x.j) : scale x%2=0 := by
  rcases x with ⟨j,b⟩
  change 0<j at hj
  change (4^j)%2=0
  cases j with
  | zero => omega
  | succ j =>
      rw [Nat.pow_succ]
      rw [Nat.mul_mod]
      simp

theorem nonempty_closed_slope_even_start {K : Nat} {x : Letter}
    {xs : List Letter} {d : Nat}
    (h : SlopeWalk K (x::xs) d d) (hK : K%2=0) (hj : 0<x.j) :
    d%2=0 := by
  cases h with
  | @cons _ _ _ e _ head tail =>
      have hs := scale_even2 x hj
      have hdiv : 2∣scale x := Nat.dvd_of_mod_eq_zero hs
      obtain ⟨q,hq⟩ := hdiv
      have hleft : scale x*e=2*(q*e) := by rw [hq]; ac_rfl
      rw [hleft] at head
      omega

/-- The doubled typed-period case: if the second half has the same exponents
    and flipped E/S types, a primitive exponent half cannot support a closed
    strict-cone slope cycle. The proof closes the two equal-gap halves, halves
    the even slope recurrence, and applies the finite valuation packing bound. -/
theorem no_doubled_gap_slope_cycle
    (x : Letter) (xs : List Letter) {d : Nat}
    (h : SlopeWalk (T ((x::xs)++flipWord (x::xs)))
      ((x::xs)++flipWord (x::xs)) d d)
    (hj : ∀ y : Letter, y∈x::xs → 0<y.j)
    (hlarge : ∃ y : Letter, y∈x::xs ∧ 1<y.j)
    (hd : 0<d)
    (hcone : 3*d<T ((x::xs)++flipWord (x::xs)))
    (hprim : CyclicPrimitive (by simp : 0<(x::xs).length)
      (slopeExponentFun (x::xs))) : False := by
  let core := x::xs
  let full := core++flipWord core
  have hmid := doubled_midpoint h
  obtain ⟨m,h1,h2,hmd⟩ := hmid
  subst m
  have hT : T full=6*(J core+core.length) := by
    dsimp [full]
    exact T_double_flip core
  have hKeven : T full%2=0 := by rw [hT]; omega
  have hxj : 0<x.j := hj x (by simp)
  have hdeven : d%2=0 := by
    apply nonempty_closed_slope_even_start h1 hKeven
    exact hxj
  have hh := halve_slopeWalk h1 hKeven hdeven (by
    intro y hy
    exact hj y (by simpa [core] using hy))
  have hhalf : SlopeWalk (T full/2) core (d/2) (d/2) := hh.2
  have hdhalf : 0<d/2 := by omega
  have hconefull : 3*d<T full := by simpa [full,core] using hcone
  have hconehalf : 3*(d/2)<T full/2 := by
    have hT2 : T full=2*(T full/2) := by omega
    have hd2 : d=2*(d/2) := by omega
    omega
  obtain ⟨ds,hds⟩ := slopeWalk_sources_exists hhalf
  have hnodup : ds.Nodup := closedSlope_sources_nodup hds
    (by intro y hy; exact hj y (by simpa [core] using hy))
    hdhalf hconehalf (by simp [core]) (by simpa [core] using hprim)
  obtain ⟨es,hvs,hjs⟩ := slopeWalkSources_edges hds
    (by intro y hy; exact hj y (by simpa [core] using hy))
    hdhalf hconehalf
  have hesnodup : (es.map (fun e => e.v)).Nodup := by rwa [hvs]
  have hJpos : 0<J core := by
    dsimp [core,J]
    omega
  have hjcore : ∀ y : Letter, y∈core → 0<y.j := by
    intro y hy
    exact hj y (by simpa [core] using hy)
  have hlargeCore : ∃ y : Letter, y∈core ∧ 1<y.j := by
    simpa [core] using hlarge
  have hlen1 : core.length+1≤J core :=
    length_add_one_le_J_of_large core hjcore hlargeCore
  have hlenpos : 0<core.length := by simp [core]
  have hKpos : 0<T full/2 := by rw [hT]; omega
  have hlow : 3*J core+2≤T full/2 := by rw [hT]; omega
  have hhigh : T full/2+4≤7*J core := by rw [hT]; omega
  have hcap := exact_edge_family_capacity (T full/2) es hKpos hesnodup
  rw [hjs] at hcap
  have hexceed := typed_cost_exceeds_capacity (T full/2) (J core)
    hKpos hlow hhigh
  omega

#print axioms no_doubled_gap_slope_cycle
#print axioms doubled_midpoint
#print axioms halve_slopeWalk
end PeriodicMacro
