import JumpResidueSource
import ResiduePeriod

namespace BB6.Agent9JumpResidue

open BB6.Agent23ResiduePeriod
open BB6.Agent45ReverseBlock (corr digits)
open BB6.Agent45WeightedDigitGap (digitWeight)

/-- Rep is invariant under changing its target by a multiple of the modulus. -/
theorem rep_congr (M x y : Int) (ws : List Int)
    (hxy : M ∣ x-y) : Rep M x ws ↔ Rep M y ws := by
  induction ws generalizing x y with
  | nil =>
    simp only [Rep,Int.dvd_iff_emod_eq_zero]
    have hmod0 : (x-y)%M=0 := Int.dvd_iff_emod_eq_zero.mp hxy
    have hmod : x%M=y%M :=
      Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr hmod0
    rw [hmod]
  | cons w ws ih =>
    simp only [Rep]
    constructor
    · rintro (h|h)
      · exact Or.inl ((ih x y hxy).mp h)
      · have hxy' : M ∣ (x-w)-(y-w) := by
          have heq : (x-w)-(y-w)=x-y := by omega
          rw [heq]
          exact hxy
        exact Or.inr ((ih (x-w) (y-w) hxy').mp h)
    · rintro (h|h)
      · exact Or.inl ((ih x y hxy).mpr h)
      · have hxy' : M ∣ (x-w)-(y-w) := by
          have heq : (x-w)-(y-w)=x-y := by omega
          rw [heq]
          exact hxy
        exact Or.inr ((ih (x-w) (y-w) hxy').mpr h)

/-- Cast a natural divisibility witness across a truncated subtraction. -/
theorem nat_sub_dvd_int (a b m d : Nat) (hba : b ≤ a)
    (h : a-b = m*d) :
    (m:Int) ∣ (a:Int)-(b:Int) := by
  have hc := congrArg (fun n : Nat => (n:Int)) h
  rw [Int.ofNat_sub hba,Int.natCast_mul] at hc
  exact ⟨(d:Int),hc⟩

/-- All (unreduced) subset sums of a finite weight list. Duplicates are
    intentional: membership, rather than list cardinality, is the interface. -/
def subsetSums : List Int → List Int
  | [] => [0]
  | w::ws =>
      let old := subsetSums ws
      old ++ old.map (fun s => s+w)

/-- A target is represented by a subset exactly when it differs from one of
    the generated subset sums by a multiple of the modulus. -/
theorem mem_subsetSums_iff (M x : Int) (ws : List Int) :
    (∃ s, s ∈ subsetSums ws ∧ M ∣ x-s) ↔ Rep M x ws := by
  induction ws generalizing x with
  | nil =>
    simp [subsetSums, Rep]
  | cons w ws ih =>
    simp only [subsetSums,List.mem_append,List.mem_map]
    constructor
    · rintro ⟨s,(hs|⟨t,ht,rfl⟩),hdiv⟩
      · exact Or.inl ((ih x).mp ⟨s,hs,hdiv⟩)
      · have hdiv' : M ∣ (x-w)-t := by
          rcases hdiv with ⟨d,hd⟩
          refine ⟨d,?_⟩
          omega
        exact Or.inr ((ih (x-w)).mp ⟨t,ht,hdiv'⟩)
    · rintro (h|h)
      · obtain ⟨s,hs,hdiv⟩ := (ih x).mpr h
        exact ⟨s,Or.inl hs,hdiv⟩
      · obtain ⟨t,ht,hdiv⟩ := (ih (x-w)).mpr h
        rcases hdiv with ⟨d,hd⟩
        refine ⟨t+w,Or.inr ⟨t,ht,rfl⟩,?_⟩
        exact ⟨d,by omega⟩

/-- Exponent and remaining weights after Agent23's exact top-factor stripping. -/
def reducedExponent (q k : Nat) : Nat :=
  (reduce k (weights q k)).1

def reducedWeights (q k : Nat) : List Int :=
  (reduce k (weights q k)).2

def reducedModulus (q k : Nat) : Nat :=
  2^(reducedExponent q k)

/-- Carry residues Y-subsetSum modulo the reduced power of two. -/
def reducedResidues (q k Y : Nat) : List Int :=
  (subsetSums (reducedWeights q k)).map
    (fun s => ((Y:Int)-s) % (reducedModulus q k : Int))

/-- Lift reduced residues into the original strict carry interval [0,q). -/
def reducedLiftResidues (q k Y : Nat) : List Nat :=
  let M := reducedModulus q k
  ((List.range (q/M+1)).flatMap
    (fun j => (reducedResidues q k Y).map (fun x => j*M+x.toNat))).filter (·<q)

theorem reducedExponent_le (q k : Nat) :
    reducedExponent q k ≤ k := by
  exact reduce_le k (weights q k)

theorem reducedResidues_range (q k Y : Nat) {x : Int}
    (hx : x ∈ reducedResidues q k Y) :
    0 ≤ x ∧ x < (reducedModulus q k : Int) := by
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx
  have hM : (0:Int) < (reducedModulus q k : Int) := by
    exact_mod_cast Nat.two_pow_pos (reducedExponent q k)
  exact ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ hM⟩

/-- The reduced residue list is exactly the Rep support of the stripped
    weight list, with no false positives or false negatives. -/
theorem mem_reducedResidues_iff (q k Y r : Nat)
    (hr : r < reducedModulus q k) :
    (r:Int) ∈ reducedResidues q k Y ↔
      Rep (reducedModulus q k : Int) ((Y:Int)-(r:Int))
        (reducedWeights q k) := by
  have hr0 : (0:Int) ≤ r := by omega
  have hrM : (r:Int) < (reducedModulus q k : Int) := by exact_mod_cast hr
  constructor
  · intro h
    obtain ⟨s,hs,hEq⟩ := List.mem_map.mp h
    have hdiv := (residue_eq_iff _ _ _ _ hr0 hrM).mp hEq.symm
    exact (mem_subsetSums_iff _ _ _).mp ⟨s,hs,hdiv⟩
  · intro h
    obtain ⟨s,hs,hdiv⟩ := (mem_subsetSums_iff _ _ _).mpr h
    have hEq := (residue_eq_iff _ _ _ _ hr0 hrM).mpr hdiv
    exact List.mem_map.mpr ⟨s,hs,hEq.symm⟩

/-- The original modular JumpMember condition is equivalent to Rep at the
    reduced modulus. -/
theorem jump_member_iff_reduced (q k Y c : Nat) :
    BB6.Agent9ReverseBlock.JumpMember (q+k) k Y c ↔
      c < q ∧
      Rep (reducedModulus q k : Int) ((Y:Int)-(c:Int))
        (reducedWeights q k) := by
  let M : Nat := 2^k
  let cmod : Nat := c % M
  have hMpos : 0 < M := Nat.two_pow_pos k
  have hcmod0 : (0:Int) ≤ (cmod:Int) := by omega
  have hcmodM : (cmod:Int) < (M:Int) := by exact_mod_cast Nat.mod_lt c hMpos
  have h0 : ∀ q, weight q 0 0 = 0 := by
    intro q
    simp [weight,corr]
  have hzero : ∀ q k B, B < 2^k → weight q (k+1) B = weight q k B := by
    intro q k B hB
    exact weight_zero q k B hB
  have hone : ∀ q k B, B < 2^k →
      weight q (k+1) (B+2^k) = weight q k B + ((q+k)*2^k : Nat) := by
    intro q k B hB
    exact weight_one q k B hB
  have hred0 := reduced_weight_iff weight h0 hzero hone q k
    (Y:Int) (cmod:Int) hcmod0 hcmodM
  have hred :
      (∃ B, B < 2^k ∧
        (cmod:Int) = ((Y:Int)-weight q k B) % (2:Int)^k) ↔
      Rep (reducedModulus q k : Int) ((Y:Int)-(cmod:Int))
        (reducedWeights q k) := by
    simpa [reducedModulus,reducedExponent,reducedWeights] using hred0
  have hmod :
      BB6.Agent9ReverseBlock.JumpMember (q+k) k Y c ↔
      c < q ∧
      (∃ B, B < 2^k ∧
        (cmod:Int) = ((Y:Int)-weight q k B) % (2:Int)^k) := by
    constructor
    · rintro ⟨hc,B,hB,hres⟩
      have hc' : c < q := by simpa [Nat.add_sub_cancel_left] using hc
      have hres' : c % M =
          (Y % M + M - (q*B+digitWeight k B)%M)%M := by
        simpa [M,Nat.add_sub_cancel_left] using hres
      have hS := nat_sub_residue M Y (q*B+digitWeight k B) hMpos
      have he : (cmod:Int) =
          ((Y:Int)-weight q k B) % (M:Int) := by
        rw [weight_eq_nat q k B hB]
        rw [←hS]
        exact congrArg (fun n : Nat => (n:Int)) hres'
      exact ⟨hc',B,hB,by simpa [cmod,M] using he⟩
    · rintro ⟨hc,B,hB,he⟩
      have hS := nat_sub_residue M Y (q*B+digitWeight k B) hMpos
      have he' := he
      change (cmod:Int) = ((Y:Int)-weight q k B) % (M:Int) at he'
      rw [weight_eq_nat q k B hB] at he'
      rw [←hS] at he'
      have hres' : cmod =
          (Y % M + M - (q*B+digitWeight k B)%M)%M := by
        exact_mod_cast he'
      refine ⟨by simpa [Nat.add_sub_cancel_left] using hc,B,hB,?_⟩
      simpa [cmod,M,Nat.add_sub_cancel_left] using hres'
  have hbigEq : c-cmod = 2^k*(c/2^k) := by
    have hdiv := Nat.div_add_mod c M
    have hdiv' : c/2^k*2^k+cmod=c := by
      simpa [M,cmod,Nat.mul_comm] using hdiv
    calc
      c-cmod = (c/2^k*2^k+cmod)-cmod := by rw [hdiv']
      _ = c/2^k*2^k := Nat.add_sub_cancel_right _ _
      _ = 2^k*(c/2^k) := Nat.mul_comm _ _
  have hbig : 2^k ∣ c-cmod := ⟨c/2^k,hbigEq⟩
  have hsmall : reducedModulus q k ∣ c-cmod :=
    Nat.dvd_trans (Nat.pow_dvd_pow 2 (reducedExponent_le q k)) hbig
  have hsmallInt : (reducedModulus q k : Int) ∣
      (c:Int)-(cmod:Int) := by
    rcases hsmall with ⟨d,hd⟩
    exact nat_sub_dvd_int c cmod (reducedModulus q k) d
      (Nat.mod_le c M) hd
  have hxy : (reducedModulus q k : Int) ∣
      ((Y:Int)-(cmod:Int))-((Y:Int)-(c:Int)) := by
    have heq : ((Y:Int)-(cmod:Int))-((Y:Int)-(c:Int)) =
        (c:Int)-(cmod:Int) := by omega
    rw [heq]; exact hsmallInt
  have hcong :
      Rep (reducedModulus q k : Int) ((Y:Int)-(cmod:Int))
        (reducedWeights q k) ↔
      Rep (reducedModulus q k : Int) ((Y:Int)-(c:Int))
        (reducedWeights q k) :=
    rep_congr _ _ _ _ hxy
  constructor
  · intro h
    rcases hmod.mp h with ⟨hc,hB⟩
    exact ⟨hc,hcong.mp (hred.mp hB)⟩
  · rintro ⟨hc,hRep⟩
    exact hmod.mpr ⟨hc,hred.mpr (hcong.mpr hRep)⟩

/-- Exact equivalence between the reduced subset-sum lift and the original
    modular JumpMember set. -/
theorem mem_reducedLift_iff (q k Y c : Nat) :
    c ∈ reducedLiftResidues q k Y ↔
      BB6.Agent9ReverseBlock.JumpMember (q+k) k Y c := by
  let M := reducedModulus q k
  have hMpos : 0 < M := Nat.two_pow_pos (reducedExponent q k)
  constructor
  · intro h
    change c ∈ ((List.range (q/M+1)).flatMap
      (fun j => (reducedResidues q k Y).map (fun x => j*M+x.toNat))).filter (·<q) at h
    obtain ⟨hlist,hcBool⟩ := List.mem_filter.mp h
    have hc : c < q := of_decide_eq_true hcBool
    obtain ⟨j,hj,hitems⟩ := List.mem_flatMap.mp hlist
    obtain ⟨x,hx,hEq⟩ := List.mem_map.mp hitems
    have hxrange := reducedResidues_range q k Y hx
    have hxcast : (x.toNat:Int)=x := Int.toNat_of_nonneg hxrange.1
    have hxnat : x.toNat < M := by
      have hxnat' : (x.toNat:Int) < (M:Int) := by simpa [hxcast] using hxrange.2
      exact_mod_cast hxnat'
    have hmod : c%M=x.toNat := by
      rw [←hEq,Nat.mul_comm j M,Nat.mul_add_mod,Nat.mod_eq_of_lt hxnat]
    have hxmem : (x.toNat:Int) ∈ reducedResidues q k Y := by
      simpa [hxcast] using hx
    have hRepX := (mem_reducedResidues_iff q k Y x.toNat hxnat).mp hxmem
    have hdiff : c-x.toNat = M*j := by rw [Nat.mul_comm M j]; omega
    have hdivInt : (M:Int) ∣ (c:Int)-(x.toNat:Int) :=
      nat_sub_dvd_int c x.toNat M j (by omega) hdiff
    have hxy : (M:Int) ∣
        ((Y:Int)-(x.toNat:Int))-((Y:Int)-(c:Int)) := by
      have heq : ((Y:Int)-(x.toNat:Int))-((Y:Int)-(c:Int)) =
          (c:Int)-(x.toNat:Int) := by omega
      rw [heq]; exact hdivInt
    have hRepC := (rep_congr (M:Int) ((Y:Int)-(x.toNat:Int))
      ((Y:Int)-(c:Int)) (reducedWeights q k) hxy).mp hRepX
    exact (jump_member_iff_reduced q k Y c).mpr ⟨hc,hRepC⟩
  · intro hJ
    rcases (jump_member_iff_reduced q k Y c).mp hJ with ⟨hc,hRep⟩
    let r := c%M
    have hr : r<M := Nat.mod_lt c hMpos
    have hdivEq : c-r = M*(c/M) := by
      have hdiv := Nat.div_add_mod c M
      have hdiv' : c/M*M+r=c := by simpa [r,Nat.mul_comm] using hdiv
      calc
        c-r = (c/M*M+r)-r := by rw [hdiv']
        _ = c/M*M := Nat.add_sub_cancel_right _ _
        _ = M*(c/M) := Nat.mul_comm _ _
    have hdivInt : (M:Int) ∣ (c:Int)-(r:Int) :=
      nat_sub_dvd_int c r M (c/M) (Nat.mod_le c M) hdivEq
    have hxy : (M:Int) ∣
        ((Y:Int)-(r:Int))-((Y:Int)-(c:Int)) := by
      have heq : ((Y:Int)-(r:Int))-((Y:Int)-(c:Int)) =
          (c:Int)-(r:Int) := by omega
      rw [heq]; exact hdivInt
    have hRepR := (rep_congr (M:Int) ((Y:Int)-(r:Int))
      ((Y:Int)-(c:Int)) (reducedWeights q k) hxy).mpr hRep
    have hres : (r:Int) ∈ reducedResidues q k Y :=
      (mem_reducedResidues_iff q k Y r hr).mpr hRepR
    have hj : c/M ∈ List.range (q/M+1) := by
      apply List.mem_range.mpr
      have hle : c/M ≤ q/M := Nat.div_le_div_right (show c≤q by omega)
      omega
    have hitems : c ∈ (reducedResidues q k Y).map
        (fun x => (c/M)*M+x.toNat) := by
      apply List.mem_map.mpr
      refine ⟨(r:Int),hres,?_⟩
      rw [Int.toNat_natCast]
      change (c/M)*M+c%M=c
      rw [Nat.mul_comm (c/M) M]
      exact Nat.div_add_mod c M
    have hflat : c ∈ (List.range (q/M+1)).flatMap
        (fun j => (reducedResidues q k Y).map (fun x => j*M+x.toNat)) := by
      exact List.mem_flatMap.mpr ⟨c/M,hj,by simpa using hitems⟩
    exact List.mem_filter.mpr ⟨hflat,by simp [hc]⟩

/-- The reduced generator is a complete BB6.Agent9ReverseBlock.JumpCover for every suffix. -/
theorem reducedLiftResidues_cover (q : Nat) (ys : List Nat) :
    BB6.Agent9ReverseBlock.JumpCover (q+ys.length) ys
      (reducedLiftResidues q ys.length (BB6.Agent45ReverseBlock.digits ys)) := by
  intro c hc
  exact (mem_reducedLift_iff q ys.length (digits ys) c).2 hc

/-- For F=q+r congruent to 24 mod 32, the exact reducer removes at least five
    binary modulus levels whenever r≥8. -/
theorem reducedExponent_final24 (q r h : Nat)
    (hr : 8 ≤ r) (hq : q+r=32*h+24) :
    reducedExponent q r ≤ r-5 := by
  have hk : q+(r-8)=32*h+16 := by omega
  have hEq : r=(r-8)+8 := by omega
  unfold reducedExponent
  rw [hEq]
  have hh := final24_reduced q (r-8) h hk
  omega

#print axioms reducedExponent_le
#print axioms reducedResidues_range
#print axioms rep_congr
#print axioms mem_subsetSums_iff
#print axioms mem_reducedResidues_iff
#print axioms jump_member_iff_reduced
#print axioms mem_reducedLift_iff
#print axioms reducedLiftResidues_cover
#print axioms reducedExponent_final24

/-- A single deduplicated negative subset-sum support is reusable at every
    target sharing q,k. Reduction after each weight is exact. -/
def modularNeg (M : Int) : List Int → List Int
  | [] => [0 % M]
  | w::ws =>
    let old := modularNeg M ws
    (old ++ old.map (fun x => (x-w)%M)).eraseDups

theorem modularNeg_mem (M : Int) (ws : List Int) (x : Int) :
    x ∈ modularNeg M ws ↔
      x ∈ (subsetSums ws).map (fun s => (-s)%M) := by
  induction ws generalizing x with
  | nil => simp [modularNeg,subsetSums]
  | cons w ws ih =>
    simp only [modularNeg,List.mem_eraseDups,List.mem_append,List.mem_map,
      subsetSums,List.map_append]
    rw [ih]
    constructor
    · rintro (h|⟨a,ha,rfl⟩)
      · exact Or.inl h
      · have ha' := (ih a).mp ha
        obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ha'
        right
        refine ⟨s+w,⟨s,hs,rfl⟩,?_⟩
        rw [Int.emod_sub_emod]
        congr 1 <;> omega
    · rintro (h|⟨a,⟨s,hs,rfl⟩,rfl⟩)
      · exact Or.inl h
      · right
        refine ⟨(-s)%M,(ih _).mpr (List.mem_map.mpr ⟨s,hs,rfl⟩),?_⟩
        rw [Int.emod_sub_emod]
        congr 1 <;> omega

theorem reducedResidues_translate (q k Y : Nat) :
    reducedResidues q k Y =
      (reducedResidues q k 0).map
        (fun x => ((Y:Int)+x) % (reducedModulus q k : Int)) := by
  unfold reducedResidues
  rw [List.map_map]
  apply List.map_congr_left
  intro s hs
  simp only [Function.comp_apply,Int.natCast_zero,Int.zero_sub]
  rw [Int.add_emod_emod]
  congr 1

/-- Membership, independent of sorting, deduplication and target translation. -/
def sharedSupport (q k : Nat) : List Int :=
  (modularNeg (reducedModulus q k : Int) (reducedWeights q k)).mergeSort

def sharedResidues (q k Y : Nat) : List Int :=
  (sharedSupport q k).map (fun x => ((Y:Int)+x) % (reducedModulus q k : Int))

theorem sharedResidues_mem (q k Y : Nat) (x : Int) :
    x ∈ sharedResidues q k Y ↔ x ∈ reducedResidues q k Y := by
  rw [reducedResidues_translate]
  simp only [sharedResidues,sharedSupport,List.mem_map,List.mem_mergeSort,
    modularNeg_mem,reducedResidues,Int.natCast_zero,Int.zero_sub]

def sharedLift (q k Y : Nat) : List Nat :=
  let M := reducedModulus q k
  ((List.range (q/M+1)).flatMap
    (fun j => (sharedResidues q k Y).map (fun x => j*M+x.toNat))).filter (·<q)

theorem sharedLift_mem (q k Y c : Nat) :
    c ∈ sharedLift q k Y ↔ c ∈ reducedLiftResidues q k Y := by
  simp only [sharedLift,reducedLiftResidues,List.mem_filter,List.mem_flatMap,
    List.mem_map,sharedResidues_mem]

theorem sharedLift_cover (q : Nat) (ys : List Nat) :
    BB6.Agent9ReverseBlock.JumpCover (q+ys.length) ys
      (sharedLift q ys.length (digits ys)) := by
  intro c hc
  exact (sharedLift_mem q ys.length (digits ys) c).2
    (reducedLiftResidues_cover q ys c hc)

#print axioms modularNeg_mem
#print axioms reducedResidues_translate
#print axioms sharedResidues_mem
#print axioms sharedLift_mem
#print axioms sharedLift_cover

end BB6.Agent9JumpResidue
