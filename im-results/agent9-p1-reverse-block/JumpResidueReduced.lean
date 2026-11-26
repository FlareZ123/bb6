import JumpResidueSource
import ResiduePeriod

namespace BB6.Agent9JumpResidue

open BB6.Agent23ResiduePeriod
open BB6.Agent45ReverseBlock (corr)
open BB6.Agent45WeightedDigitGap (digitWeight)
open BB6.Agent9ReverseBlock (digits JumpMember JumpCover)

/-- Rep is invariant under changing its target by a multiple of the modulus. -/
theorem rep_congr (M x y : Int) (ws : List Int)
    (hxy : M ∣ x-y) : Rep M x ws ↔ Rep M y ws := by
  induction ws generalizing x y with
  | nil =>
    simp only [Rep]
    constructor
    · rintro ⟨a,ha⟩
      rcases hxy with ⟨b,hb⟩
      have hy : y = M*a-M*b := by omega
      refine ⟨a-b,?_⟩
      calc
        y = M*a-M*b := hy
        _ = M*(a-b) := by rw [← mul_sub]
    · rintro ⟨a,ha⟩
      rcases hxy with ⟨b,hb⟩
      have hx : x = M*a+M*b := by omega
      refine ⟨a+b,?_⟩
      calc
        x = M*a+M*b := hx
        _ = M*(a+b) := by rw [← mul_add]
  | cons w ws ih =>
    simp only [Rep]
    constructor
    · rintro (h|h)
      · exact Or.inl ((ih x y hxy).mp h)
      · have hxy' : M ∣ (x-w)-(y-w) := by
          rcases hxy with ⟨d,hd⟩
          refine ⟨d,?_⟩
          have heq : (x-w)-(y-w)=x-y := by omega
          rw [heq]
          exact hd
        exact Or.inr ((ih (x-w) (y-w) hxy').mp h)
    · rintro (h|h)
      · exact Or.inl ((ih x y hxy).mpr h)
      · have hxy' : M ∣ (x-w)-(y-w) := by
          rcases hxy with ⟨d,hd⟩
          refine ⟨d,?_⟩
          have heq : (x-w)-(y-w)=x-y := by omega
          rw [heq]
          exact hd
        exact Or.inr ((ih (x-w) (y-w) hxy').mpr h)

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

/-- The original JumpMember condition is equivalent to Rep at the reduced
    modulus. The only lost low bits are precisely the top factors removed by
    reduce_sound; c and c mod 2^k are interchangeable at the reduced modulus. -/
theorem jump_member_iff_reduced (q k Y c : Nat) :
    JumpMember (q+k) k Y c ↔
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
      JumpMember (q+k) k Y c ↔
      c < q ∧
      (∃ B, B < 2^k ∧
        (cmod:Int) = ((Y:Int)-weight q k B) % (2:Int)^k) := by
    constructor
    · rintro ⟨hc,B,hB,hres⟩
      have hc' : c < q := by simpa using hc
      refine ⟨hc',B,hB,?_⟩
      have hcast : (cmod:Int) =
          (((Y % 2^k + 2^k -
            (q*B+digitWeight k B)%2^k)%2^k : Nat) : Int) := by
        exact_mod_cast hres
      have hsub := nat_sub_residue (2^k) Y
        (q*B+digitWeight k B) hMpos
      calc
        (cmod:Int) =
          (((Y % 2^k + 2^k -
            (q*B+digitWeight k B)%2^k)%2^k : Nat) : Int) := hcast
        _ = ((Y:Int)-(q*B+digitWeight k B:Int)) % (2:Int)^k := hsub
        _ = ((Y:Int)-weight q k B) % (2:Int)^k := by
          rw [weight_eq_nat q k B hB]
    · rintro ⟨hc,B,hB,hres⟩
      refine ⟨by simpa using hc,B,hB,?_⟩
      have hsub := nat_sub_residue (2^k) Y
        (q*B+digitWeight k B) hMpos
      have hcast : (cmod:Int) =
          (((Y % 2^k + 2^k -
            (q*B+digitWeight k B)%2^k)%2^k : Nat) : Int) := by
        calc
          (cmod:Int) = ((Y:Int)-weight q k B) % (2:Int)^k := hres
          _ = ((Y:Int)-(q*B+digitWeight k B:Int)) % (2:Int)^k := by
            rw [weight_eq_nat q k B hB]
          _ = _ := hsub.symm
      exact_mod_cast hcast
  have hbig : 2^k ∣ c-cmod := by
    refine ⟨c/2^k,?_⟩
    have h := Nat.div_add_mod c (2^k)
    omega
  have hsmall : reducedModulus q k ∣ c-cmod :=
    Nat.dvd_trans (Nat.pow_dvd_pow 2 (reducedExponent_le q k)) hbig
  have hsmallInt : (reducedModulus q k : Int) ∣
      (c:Int)-(cmod:Int) := by
    rcases hsmall with ⟨d,hd⟩
    refine ⟨(d:Int),?_⟩
    exact_mod_cast hd
  have hcong :
      Rep (reducedModulus q k : Int) ((Y:Int)-(cmod:Int))
        (reducedWeights q k) ↔
      Rep (reducedModulus q k : Int) ((Y:Int)-(c:Int))
        (reducedWeights q k) := by
    apply rep_congr
    convert hsmallInt using 1 <;> omega
  constructor
  · intro h
    rcases hmod.mp h with ⟨hc,hB⟩
    exact ⟨hc,hcong.mp (hred.mp hB)⟩
  · rintro ⟨hc,hRep⟩
    exact hmod.mpr ⟨hc,hred.mpr (hcong.mpr hRep)⟩

/-- Exact equivalence between the reduced subset-sum lift and the original
    modular JumpMember set. -/
theorem mem_reducedLift_iff (q k Y c : Nat) :
    c ∈ reducedLiftResidues q k Y ↔ JumpMember (q+k) k Y c := by
  let M := reducedModulus q k
  have hMpos : 0 < M := Nat.two_pow_pos (reducedExponent q k)
  constructor
  · intro h
    change c ∈ ((List.range (q/M+1)).flatMap
      (fun j => (reducedResidues q k Y).map (fun x => j*M+x.toNat))).filter (·<q) at h
    obtain ⟨hlist,hc⟩ := List.mem_filter.mp h
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
    have hdiff : c-x.toNat = j*M := by omega
    have hdivNat : M ∣ c-x.toNat := by
      refine ⟨j,?_⟩
      simpa [Nat.mul_comm] using hdiff
    have hdivInt : (M:Int) ∣ (c:Int)-(x.toNat:Int) := by
      rcases hdivNat with ⟨d,hd⟩
      refine ⟨(d:Int),?_⟩
      exact_mod_cast hd
    have hRepC : Rep (M:Int) ((Y:Int)-(c:Int))
        (reducedWeights q k) := by
      apply (rep_congr (M:Int) ((Y:Int)-(x.toNat:Int))
        ((Y:Int)-(c:Int)) (reducedWeights q k) ?_).mp hRepX
      convert hdivInt using 1 <;> omega
    exact (jump_member_iff_reduced q k Y c).mpr ⟨hc,hRepC⟩
  · intro hJ
    rcases (jump_member_iff_reduced q k Y c).mp hJ with ⟨hc,hRep⟩
    let r := c%M
    have hr : r<M := Nat.mod_lt c hMpos
    have hdivNat : M ∣ c-r := by
      have h : M*(c/M)+r=c := by
        simpa [r,Nat.mul_comm] using Nat.div_add_mod c M
      refine ⟨c/M,?_⟩
      omega
    have hdivInt : (M:Int) ∣ (c:Int)-(r:Int) := by
      rcases hdivNat with ⟨d,hd⟩
      refine ⟨(d:Int),?_⟩
      exact_mod_cast hd
    have hRepR : Rep (M:Int) ((Y:Int)-(r:Int))
        (reducedWeights q k) := by
      apply (rep_congr (M:Int) ((Y:Int)-(r:Int))
        ((Y:Int)-(c:Int)) (reducedWeights q k) ?_).mpr hRep
      convert hdivInt using 1 <;> omega
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
      have h := Nat.div_add_mod c M
      simpa [r,Nat.mul_comm] using h
    have hflat : c ∈ (List.range (q/M+1)).flatMap
        (fun j => (reducedResidues q k Y).map (fun x => j*M+x.toNat)) := by
      exact List.mem_flatMap.mpr ⟨c/M,hj,by simpa using hitems⟩
    exact List.mem_filter.mpr ⟨hflat,hc⟩

/-- The reduced generator is a complete JumpCover for every suffix. -/
theorem reducedLiftResidues_cover (q : Nat) (ys : List Nat) :
    JumpCover (q+ys.length) ys
      (reducedLiftResidues q ys.length (digits ys)) := by
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

#print axioms rep_congr
#print axioms mem_subsetSums_iff
#print axioms mem_reducedResidues_iff
#print axioms jump_member_iff_reduced
#print axioms mem_reducedLift_iff
#print axioms reducedLiftResidues_cover
#print axioms reducedExponent_final24

end BB6.Agent9JumpResidue
