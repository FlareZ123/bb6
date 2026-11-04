import BB429NewResidue
import Lean.Elab.Tactic.Omega

/-!
A source-connected exact inverse exclusion of an infinite remaining
1021-mod-1024 halting sector for the genuine blank-root BB429 machine.
This imports the unchanged original BB429.next and its kernel-verified
all-time modular invariant. No finite cutoff is assumed.
-/

namespace BB429No1021

open BB429NewResidue

set_option maxHeartbeats 10000000

private theorem odd_force (a b na nb : Nat)
    (ha : 13 ≤ a) (ho : a%2=1)
    (hf : a=2*na+3 ∧ nb=b+a)
    (hs : ∀ x y, 4*x+26=4*a+b → 2*y=b+4 → b%4=2 →
      ¬ BB429Mod8.Allowed x y)
    (hr : Reach a b) : Reach na nb := by
  rcases odd_back a b ha ho hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he : x=na ∧ y=nb := by omega
    rcases he with ⟨rfl,rfl⟩
    exact hp
  · exact False.elim (hs x y hx hy hw (reach_allowed x y hp))

/-- The full reverse tree has one forced primary branch per level.
All alternate parents contradict the actual-root Allowed invariant. -/
private theorem exclude (q : Nat) :
    ¬ Reach (16384*q+12285) (32768*q+24569) := by
  intro h0
  have h1 : Reach (8192*q+6141) (49152*q+36854) := by
    apply odd_force (16384*q+12285) (32768*q+24569) (8192*q+6141) (49152*q+36854)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h0
  have h2 : Reach (4096*q+3069) (57344*q+42995) := by
    apply odd_force (8192*q+6141) (49152*q+36854) (4096*q+3069) (57344*q+42995)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h1
  have h3 : Reach (2048*q+1533) (61440*q+46064) := by
    apply odd_force (4096*q+3069) (57344*q+42995) (2048*q+1533) (61440*q+46064)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h2
  have h4 : Reach (1024*q+765) (63488*q+47597) := by
    apply odd_force (2048*q+1533) (61440*q+46064) (1024*q+765) (63488*q+47597)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h3
  have h5 : Reach (512*q+381) (64512*q+48362) := by
    apply odd_force (1024*q+765) (63488*q+47597) (512*q+381) (64512*q+48362)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h4
  have h6 : Reach (256*q+189) (65024*q+48743) := by
    apply odd_force (512*q+381) (64512*q+48362) (256*q+189) (65024*q+48743)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h5
  have h7 : Reach (128*q+93) (65280*q+48932) := by
    apply odd_force (256*q+189) (65024*q+48743) (128*q+93) (65280*q+48932)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h6
  have h8 : Reach (64*q+45) (65408*q+49025) := by
    apply odd_force (128*q+93) (65280*q+48932) (64*q+45) (65408*q+49025)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h7
  have h9 : Reach (32*q+21) (65472*q+49070) := by
    apply odd_force (64*q+45) (65408*q+49025) (32*q+21) (65472*q+49070)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h8
  have h10 : Reach (16*q+9) (65504*q+49091) := by
    apply odd_force (32*q+21) (65472*q+49070) (16*q+9) (65504*q+49091)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h9
  have hx := reach_allowed _ _ h10
  unfold BB429Mod8.Allowed at hx
  omega

/-- All genuine blank-root terminal states avoid the 12285 mod 16384 sector. -/
theorem blank_halt_not_12285_mod16384 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%16384 ≠ 12285 := by
  intro hm
  let q := a/16384
  have ha : a=16384*q+12285 := by dsimp [q]; omega
  have hb : b=32768*q+24569 := by omega
  have h0 : Reach (16384*q+12285) (32768*q+24569) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact exclude q h0

#print axioms blank_halt_not_12285_mod16384

end BB429No1021
