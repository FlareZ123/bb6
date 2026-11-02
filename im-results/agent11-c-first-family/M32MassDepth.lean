import M32AllDepthOriginal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11
open BB6.Agent15

/-- Exact affine inverse normal form for every odd-part input, with no
    restriction on the original weighted mass modulo 32. -/
theorem odd_term_normalized_exact (a d q : Nat)
    (ha : a%4=3) (hq : 1≤q) :
    let k := 2^(d+1)*(2*q+1)-2
    let p := affineNormalize a k
    p.2=4*q ∧ p.1+8*q+4*d=a+2*k := by
  let k := 2^(d+1)*(2*q+1)-2
  let p := affineNormalize a k
  have hdepth : oddDepth k=d := oddDepth_odd_term d q hq
  obtain ⟨hm,hs,_⟩ := normalize_three_depth_invariants a k ha
  change p.1+2*p.2+4*oddDepth k=a+2*k at hm
  change 2^(oddDepth k)*(p.2+2)=k+2 at hs
  have hfactor : k+2=2^d*(4*q+2) := by
    dsimp [k]
    have hp : 2^(d+1)=2^d*2 := Nat.pow_succ 2 d
    rw [hp]
    have he : 2*(2*q+1)=4*q+2 := by omega
    have hraw : 2^d * 2 * (2*q+1) = 2^d*(4*q+2) := by
      rw [Nat.mul_assoc,he]
    rw [hraw]
    have hh : 2 ≤ 2^d*(4*q+2) := by
      calc
        2 ≤ 4*q+2 := by omega
        _ ≤ 2^d*(4*q+2) :=
          Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
    omega
  have hright : p.2+2 = 4*q+2 := by
    have ht : 2^d*(p.2+2) = 2^d*(4*q+2) := by
      rw [hdepth] at hs
      exact hs.trans hfactor
    exact Nat.mul_left_cancel (Nat.pow_pos (by decide)) ht
  have hp2 : p.2=4*q := by omega
  constructor
  · exact hp2
  · change p.1+8*q+4*d=a+2*k
    rw [hdepth,hp2] at hm
    omega

/-- Finite M32 forbidden cylinders tested on exact *source* mass and
    symbolic affine depth, rather than on the normalization's output. -/
def m32MassCell (mass d q : Nat) : Prop :=
  m32Cylinder
    ((mass+32*(d+q+1)-4*d-8*q)%32)
    ((4*q)%32)

/-- A general original-source theorem for arbitrarily deep backward
    affine chains and arbitrary source mass; no fixed 23-mod-32 condition. -/
theorem original_m32_mass_barrier
    (a d q : Nat) (ha : a%4=3) (hq : 1≤q)
    (hcell : m32MassCell (a+2*(2^(d+1)*(2*q+1)-2)) d q) :
    ¬ CReach a (2^(d+1)*(2*q+1)-2) := by
  intro hreach
  let k := 2^(d+1)*(2*q+1)-2
  let p := affineNormalize a k
  obtain ⟨hp2,hm⟩ := odd_term_normalized_exact a d q ha hq
  change p.2=4*q at hp2
  change p.1+8*q+4*d=a+2*k at hm
  have hp1mod :
      (a+2*k+32*(d+q+1)-4*d-8*q)%32=p.1%32 := by omega
  have hp2mod : (4*q)%32=p.2%32 := by omega
  have hc : m32Cylinder p.1 p.2 := by
    unfold m32MassCell m32Cylinder at hcell ⊢
    rw [hp1mod,hp2mod] at hcell
    exact hcell
  exact original_section_no_eight p.1 p.2 hc
    ((reach_iff_normalize a k).mp hreach)

#print axioms odd_term_normalized_exact
#print axioms original_m32_mass_barrier
end BB6.Agent11
