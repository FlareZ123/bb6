import CancellationMod7Joint
import Lean.Elab.Tactic.Omega

namespace CancellationSmallParent
open CancellationModSeven

private theorem arithmetic (n : Nat) (hn : 128 ≤ n)
    (hfive : n%5=0) (hseven : n%7=5) (heven : n%2=0) :
    ∃ p:Nat, n+3-8=35*(2*p+3) := by
  have h70 : n%70=40 := by omega
  let k:=n/70
  have hnrepr:n=70*k+40 := by dsimp [k]; omega
  have hk:1≤k := by omega
  refine ⟨k-1, ?_⟩
  omega

theorem parent_four_exists (r:Nat) (hr:1≤r) (hres:r%3=1) :
  ∃ p:Nat, 2^(valuationA r)*P (2^(valuationA r)) r+3-2*4 =
      (2^(4+1)+3)*(2*p+3) := by
  let a:=valuationA r
  let A:=2^a
  let Q:=P A r
  have ha7:7≤a := by
    have hl:=valuationA_linear r
    omega
  have hA128:128≤A := by
    have hpow:=Nat.pow_le_pow_right (by decide : 0<(2:Nat)) ha7
    dsimp [A]
    omega
  have hA3:3≤A := by omega
  have hP:0<Q := P_pos A r (by omega : 4≤A) hr
  have hAP:A≤A*Q := Nat.le_mul_of_pos_right A hP
  have hAPbig:128≤A*Q := by omega
  have hA5:A%5=3 := A_mod5 r
  have hQ5:Q%5=0 := P_mod5 A r hA3 hA5
  have hAPmod5:(A*Q)%5=0 := by rw [Nat.mul_mod,hQ5]; simp
  have hA7:A%7=2 := A_mod7 r hr
  have hQ7:Q%7=6 := by
    have hh:=P_mod7 A r hA3 hA7
    have hf:f r=6 := by simp [f,hres]
    omega
  have hAPmod7:(A*Q)%7=5 := by
    rw [Nat.mul_mod,hA7,hQ7]
  have hAeven:A%2=0 := by
    have hapos:1≤a := by omega
    have ha:a=(a-1)+1 := by omega
    dsimp [A]
    rw [ha, Nat.pow_succ, Nat.mul_mod]
    simp
  have hAPeven:(A*Q)%2=0 := by rw [Nat.mul_mod,hAeven]; simp
  exact arithmetic (A*Q) hAPbig hAPmod5 hAPmod7 hAPeven

#print axioms parent_four_exists
end CancellationSmallParent
