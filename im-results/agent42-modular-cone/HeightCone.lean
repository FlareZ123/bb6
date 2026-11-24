import ModularConeHighStop
import Lean.Elab.Tactic.Omega

namespace BB6.Agent42ModularCone

/-- Largest available precision up to cap, computed from the exact right counter. -/
def heightBits (cap y : Nat) : Nat := min cap ((y+2)/3).log2

theorem heightBits_large (cap y : Nat) (hy : 1≤y) : Large (heightBits cap y) y := by
  have hpos : (y+2)/3 ≠ 0 := by omega
  have hpow : 2^(heightBits cap y) ≤ (y+2)/3 :=
    (Nat.le_log2 hpos).mp (Nat.min_le_right _ _)
  unfold Large P
  omega

def heightExcluded (cap x y : Nat) : Bool :=
  excluded (heightBits cap y) ⟨(x:Int),(y:Int)⟩

def ExclusionSound (reach : Nat → Nat → Prop) : Prop :=
  ∀ b s, excluded b s=true → ∀ x y, Large b y → Matches b x y s → ¬reach x y

theorem height_excluded_sound (reach : Nat → Nat → Prop) (hs : ExclusionSound reach)
    (cap x y : Nat) (hy : 1≤y) (hc : heightExcluded cap x y=true) : ¬reach x y := by
  apply hs (heightBits cap y) ⟨(x:Int),(y:Int)⟩ hc x y (heightBits_large cap y hy)
  simp [Matches,Cong]

theorem height_excluded_sound_all (reach : Nat → Nat → Prop) (hs : ExclusionSound reach)
    (cap x y : Nat) (hc : heightExcluded cap x y=true) : ¬reach x y := by
  by_cases hy : 1≤y
  · exact height_excluded_sound reach hs cap x y hy hc
  · have h0 : y=0 := by omega
    subst y
    simp [heightExcluded,heightBits,excluded,check] at hc

/-- Fixed-depth stopping targets are an affine ray in the high index.
    A successful exact-target residue at the initial point certifies the
    entire upward ray, even when b exceeds 2*m+2. -/
theorem fixed_m_ray_excluded (reach : Nat → Nat → Prop) (hs : ExclusionSound reach)
    (b j0 m k0 t : Nat) (hl : Large b k0)
    (hc : excluded b ⟨(2*j0+1 : Nat),(k0:Int)⟩=true) :
    ¬reach (2*(j0+P b*t)+1) (k0+(P (2*m+2)-1)*(P b*t)) := by
  apply hs b ⟨(2*j0+1 : Nat),(k0:Int)⟩ hc
  · unfold Large at *
    omega
  · constructor
    · unfold Cong I
      refine ⟨2*(t:Int),?_⟩
      push_cast
      rw [Int.mul_add, ← Int.mul_assoc, Int.mul_comm 2 (↑(P b) : Int), Int.mul_assoc]
      omega
    · unfold Cong I
      refine ⟨((P (2*m+2)-1 : Nat):Int)*(t:Int),?_⟩
      push_cast
      rw [Int.mul_left_comm (↑(P b))]
      omega

/-- The affine ray comprises actual stopping targets whenever its base does. -/
theorem fixed_m_ray_stop (b j0 m k0 t : Nat)
    (h0 : k0+j0+3*m+4=P (2*m+2)*(j0+2)) :
    k0+(P (2*m+2)-1)*(P b*t)+(j0+P b*t)+3*m+4 =
      P (2*m+2)*((j0+P b*t)+2) := by
  have hp : 1≤P (2*m+2) := Nat.pow_pos (by decide)
  have hmul : P (2*m+2)*(P b*t) = (P (2*m+2)-1)*(P b*t)+P b*t := by
    conv => lhs; rw [show P (2*m+2) = (P (2*m+2)-1)+1 by omega]
    rw [Nat.add_mul, Nat.one_mul]
  have hsum : j0+P b*t+2=(j0+2)+P b*t := by omega
  rw [hsum,Nat.mul_add,hmul]
  omega

/-- Concrete certificate in the m=0 slice, impossible for the old b=2 filter. -/
theorem ray_12_0_certificate : excluded 3 ⟨25,40⟩=true := by decide

theorem ray_12_0_old_misses : highStopExcluded 12 0=false := by decide

theorem ray_12_0_old_misses_all (t : Nat) : highStopExcluded (12+8*t) 0=false := by
  have hj : 2≤12+8*t := by omega
  have hb : highStopBits (12+8*t) 0=2 := by simp [highStopBits,hj]
  have hr : residue 2 (stopResidue (12+8*t) 0)=residue 2 (stopResidue 12 0) := by
    simp only [residue,stopResidue,I,P,Int.natCast_add,Int.natCast_mul,Int.cast_ofNat_Int]
    congr 1 <;> omega
  unfold highStopExcluded excluded
  rw [hb,hr]
  decide

theorem ray_12_0 (reach : Nat → Nat → Prop) (hs : ExclusionSound reach) (t : Nat) :
    ¬reach (25+16*t) (40+24*t) := by
  have h := fixed_m_ray_excluded reach hs 3 12 0 40 t (by unfold Large P; decide) ray_12_0_certificate
  have hx : 2*(12+P 3*t)+1=25+16*t := by simp [P]; omega
  have hy : 40+(P (2*0+2)-1)*(P 3*t)=40+24*t := by simp [P]; omega
  rwa [hx,hy] at h

/-- Instantiate the new method with the already accepted original-source law. -/
theorem source_height_excluded (cap x y : Nat) (hc : heightExcluded cap x y=true) :
    ¬BB6.Agent3.CReach x y :=
  height_excluded_sound_all BB6.Agent3.CReach source_excluded cap x y hc

theorem source_fixed_m_ray_excluded (b j0 m k0 t : Nat) (hl : Large b k0)
    (hc : excluded b ⟨(2*j0+1 : Nat),(k0:Int)⟩=true) :
    ¬BB6.Agent3.CReach (2*(j0+P b*t)+1) (k0+(P (2*m+2)-1)*(P b*t)) :=
  fixed_m_ray_excluded BB6.Agent3.CReach source_excluded b j0 m k0 t hl hc

theorem source_ray_12_0 (t : Nat) : ¬BB6.Agent3.CReach (25+16*t) (40+24*t) :=
  ray_12_0 BB6.Agent3.CReach source_excluded t

#print axioms height_excluded_sound_all
#print axioms fixed_m_ray_excluded
#print axioms fixed_m_ray_stop
#print axioms ray_12_0_old_misses_all
#print axioms source_height_excluded
#print axioms source_fixed_m_ray_excluded
#print axioms source_ray_12_0
end BB6.Agent42ModularCone
