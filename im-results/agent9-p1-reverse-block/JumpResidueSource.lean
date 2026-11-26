import JumpResidueCore
import ReverseBlockJump

namespace BB6.Agent9JumpResidue
open BB6.Agent45ReverseBlock (digits corr)
open BB6.Agent45WeightedDigitGap (digitWeight corr_le_mul)
open BB6.Agent9ReverseBlock (JumpMember JumpCover)

theorem weight_eq_nat (q k B : Nat) (hB : B < 2^k) :
    weight q k B = (q*B+digitWeight k B : Nat) := by
  have hc := corr_le_mul k B hB
  unfold weight digitWeight
  rw [Nat.add_mul]
  rw [Int.natCast_add,Int.natCast_add,Int.ofNat_sub hc]
  omega

/-- Lift the complete set of modular residues into the broad carry range.
    This matches the nested base/residue loop at the level of set membership. -/
def liftResidues (q k Y : Nat) : List Nat :=
  let M : Nat := 2^k
  let rs := residuesUnique (M : Int) q Y k
  ((List.range (q/M+1)).flatMap
    (fun j => rs.map (fun x => j*M+x.toNat))).filter (· < q)

/-- Modular subtraction in the source's Nat representation agrees with
    Euclidean remainder of the signed difference. -/
theorem nat_sub_residue (M Y S : Nat) (hM : 0 < M) :
    ((Y%M+M-S%M)%M : Nat) = ((Y : Int)-(S : Int)) % (M : Int) := by
  have hs := Nat.mod_lt S hM
  have hle : S%M ≤ Y%M+M := by omega
  rw [← Int.ofNat_mod_ofNat,Int.ofNat_sub hle,Int.natCast_add,← Int.ofNat_mod_ofNat,← Int.ofNat_mod_ofNat]
  rw [Int.sub_emod_emod]
  rw [show (Y:Int)%(M:Int)+(M:Int)-(S:Int) =
    ((Y:Int)%(M:Int)-(S:Int))+(M:Int) by omega]
  simp

/-- Full no-false-negative bridge from source JumpMember to the concrete
    low-bit-first subset-sum generator and interval lifting. -/
theorem mem_lift_of_jump (F k Y c : Nat) (h : JumpMember F k Y c) :
    c ∈ liftResidues (F-k) k Y := by
  obtain ⟨hc,B,hB,hres⟩ := h
  let M : Nat := 2^k
  let q := F-k
  have hM : 0<M := Nat.two_pow_pos k
  have hS := nat_sub_residue M Y (q*B+digitWeight k B) hM
  have he : ((c%M : Nat) : Int) = (Y-weight q k B)%(M:Int) := by
    rw [weight_eq_nat q k B hB]
    rw [←hS]
    exact congrArg (fun n : Nat => (n : Int)) hres
  have hr : ((c%M : Nat) : Int) ∈ residuesUnique (M:Int) q Y k :=
    (mem_residuesUnique_iff (M:Int) q Y (c%M : Nat) k).2
      ((mem_residues_iff (M:Int) q Y (c%M : Nat) k).2 ⟨B,hB,he⟩)
  change c ∈ ((List.range (q/M+1)).flatMap
    (fun j => (residuesUnique (M:Int) q Y k).map (fun x => j*M+x.toNat))).filter (· < q)
  apply List.mem_filter.mpr
  refine ⟨?_, by simpa [q] using hc⟩
  apply List.mem_flatMap.mpr
  refine ⟨c/M,List.mem_range.mpr ?_,?_⟩
  · have hdiv : c/M ≤ q/M := Nat.div_le_div_right (show c≤q by omega)
    omega
  · apply List.mem_map.mpr
    refine ⟨((c%M : Nat) : Int),hr,?_⟩
    rw [Int.toNat_natCast]
    simpa [Nat.mul_comm] using Nat.div_add_mod c M

/-- The lifted set is exact, not merely a cover. -/
theorem mem_lift_iff (F k Y c : Nat) :
    c ∈ liftResidues (F-k) k Y ↔ JumpMember F k Y c := by
  refine ⟨?_,mem_lift_of_jump F k Y c⟩
  intro h
  let M : Nat := 2^k
  let q := F-k
  have hM : 0<M := Nat.two_pow_pos k
  change c ∈ ((List.range (q/M+1)).flatMap
    (fun j => (residuesUnique (M:Int) q Y k).map (fun x => j*M+x.toNat))).filter (· < q) at h
  obtain ⟨hl,hc⟩ := List.mem_filter.mp h
  obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp hl
  obtain ⟨x,hx,he⟩ := List.mem_map.mp hj
  obtain ⟨hlo,hhi⟩ := residue_range (M:Int) q Y x k (by omega) hx
  have hcast : (x.toNat : Int) = x := Int.toNat_of_nonneg hlo
  have hlt : x.toNat < M := by omega
  have hmod : c%M = x.toNat := by
    rw [←he,Nat.mul_comm j M,Nat.mul_add_mod,Nat.mod_eq_of_lt hlt]
  obtain ⟨B,hB,hxEq⟩ := (mem_residues_iff (M:Int) q Y x k).1
    ((mem_residuesUnique_iff (M:Int) q Y x k).1 hx)
  have hS := nat_sub_residue M Y (q*B+digitWeight k B) hM
  rw [weight_eq_nat q k B hB,←hS] at hxEq
  refine ⟨by simpa [q] using hc,B,hB,?_⟩
  change c%M = (Y%M+M-(q*B+digitWeight k B)%M)%M
  omega

theorem liftResidues_cover (F : Nat) (ys : List Nat) :
    JumpCover F ys (liftResidues (F-ys.length) ys.length (digits ys)) := by
  intro c hc
  exact mem_lift_of_jump F ys.length (digits ys) c hc

#print axioms weight_eq_nat
#print axioms nat_sub_residue
#print axioms mem_lift_iff
#print axioms liftResidues_cover
end BB6.Agent9JumpResidue
