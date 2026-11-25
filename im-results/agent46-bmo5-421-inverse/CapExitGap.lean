import CapSignedMacro
import CapExitRigidityCore
import CapExitWordCore

namespace CapSieve
open Bmo

theorem negative_event_small {k w j q : Nat} (hv : CapNegative.Valid k w)
    (he : (CapNegative.event k w).2=some (j,q)) : q≤3*j+12 := by
  have h := CapNegative.stop_spec hv
  unfold CapNegative.event at he
  dsimp at h he
  generalize CapNegative.stopCount k w = n at *
  generalize k+n = b at *
  generalize 3^n*w = v at *
  by_cases ht : v=2*b+3
  · simp [ht] at he
  · rw [if_neg ht] at he
    by_cases hs : v=2*b+7
    · rw [if_pos hs] at he
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj he)
      omega
    · rw [if_neg hs] at he
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj he)
      have := h.1.2.1
      omega

theorem regular_fail_product {k q : Nat} (h : PosQ k q)
    (hp : k+7≤positiveNext k q)
    (hf : positiveNext (k+1) (positiveNext k q)<k+8) :
    2*2^k≤q*positiveNext k q ∨ 4*2^k≤positiveNext k q*positiveNext k q := by
  let p := positiveNext k q
  let r := positiveNext (k+1) p
  have hq : 0<q := by have := h.1; omega
  have hpb := positive_next_bounds hq h.2.1
  have hpp : 0<p := by change 2≤p ∧ _ at hpb; omega
  have hph : p≤2*P (k+1)-2 := hpb.2
  have h1 := positive_next_equation hq h.2.1
  have h2 := positive_next_equation hpp hph
  have hr := (positive_next_bounds hpp hph).1
  change p+2*P k=3^(positiveCount k q+1)*q+3 at h1
  change r+2*P (k+1)=3^(positiveCount (k+1) p+1)*p+3 at h2
  change 2≤r at hr
  change k+7≤p at hp
  change r<k+8 at hf
  unfold P at h1 h2
  rw [Nat.pow_succ] at h2
  have he1 : 3^(positiveCount k q+1)*q+3=10*2^k+p := by omega
  have he2 : 3^(positiveCount (k+1) p+1)*p+3=20*2^k+r := by omega
  exact CapExitRigidity.regular_fail_product he1 he2 hp (by omega) hr

def relaxedExponent (k q j : Nat) : Nat :=
  positiveCount (k+j) (positiveOrbit k q j)+1

theorem relaxed_exit_word {k q : Nat} (h : PosQ k q) (t : Nat) :
    3^(CapExitWord.exponent (relaxedExponent k q) t)*q+
      3*CapExitWord.offset (relaxedExponent k q) t =
    positiveOrbit k q t+10*2^k*CapExitWord.coeff (relaxedExponent k q) t := by
  have hu := positive_orbit_upper (by have := h.1; omega : 0<q) h.2.1
  have he := CapExitWord.expansion k (relaxedExponent k q) (positiveOrbit k q) t (by
    intro j _
    have hj := positive_next_equation (hu j).1 (hu j).2
    unfold P positiveProduct at hj
    change positiveNext (k+j) (positiveOrbit k q j)+10*2^(k+j)=
      3^(positiveCount (k+j) (positiveOrbit k q j)+1)*positiveOrbit k q j+3
    omega)
  exact he

#print axioms negative_event_small
#print axioms regular_fail_product
#print axioms relaxed_exit_word
end CapSieve
