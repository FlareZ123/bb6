import BB429InverseKernel
import BB429Branch29Odd31
import Lean.Elab.Tactic.Omega

/-!
# Reusing Agent 33's sound affine inverse-tree certificate for #429

The generic proved Boolean `BB429Kernel.cert_sound` is applied directly
to the 29-mod32 odd reset line. This yields two additional full
uniform q(mod128) exclusions *without introducing a new inverse engine*.
All explicit finite Boolean certificates are kernel-checked by `decide`
and their consequences hold for arbitrarily large q.
-/

namespace BB429Branch29Reflect
open BB429Reset31
set_option maxHeartbeats 20000000
set_option maxRecDepth 30000

/-- The affine inverse-kernel's exact parameter lifting:
q=128*t+r and the symbolic (A,a,B,b) translate into
(32q+29,64q+55) for every t and any residue r<128. -/
theorem exclude_of_cert (r q d : Nat) (hr : q%128=r)
    (hc : BB429Kernel.cert d ⟨4096,32*r+29,8192,64*r+55⟩ = true) :
    ¬Reach (32*q+29) (64*q+55) := by
  intro hroot
  let t := q/128
  have hqeq : q=128*t+r := by dsimp [t]; omega
  have hx :
      BB429Kernel.va ⟨4096,32*r+29,8192,64*r+55⟩ t =
      32*q+29 := by
    simp only [BB429Kernel.va]
    omega
  have hy :
      BB429Kernel.vb ⟨4096,32*r+29,8192,64*r+55⟩ t =
      64*q+55 := by
    simp only [BB429Kernel.vb]
    omega
  obtain ⟨n,hn⟩ := hroot
  have hs : BB429NewResidue.Reach
      (BB429Kernel.va ⟨4096,32*r+29,8192,64*r+55⟩ t)
      (BB429Kernel.vb ⟨4096,32*r+29,8192,64*r+55⟩ t) :=
    ⟨n, by simpa only [hx,hy] using hn⟩
  exact (BB429Kernel.cert_sound d
    ⟨4096,32*r+29,8192,64*r+55⟩ t hc) hs

/-- Kernel-checked all-parameter inverse-tree certificate for
q=10 mod128, using Agent33's validated exact certificate machinery. -/
theorem no_q_10_mod128 (q : Nat) (hq : q%128=10) :
    ¬Reach (32*q+29) (64*q+55) := by
  apply exclude_of_cert 10 q 12 hq
  decide

/-- Kernel-checked all-parameter inverse-tree certificate for
q=122 mod128, using the same exact F/S/E predecessor program. -/
theorem no_q_122_mod128 (q : Nat) (hq : q%128=122) :
    ¬Reach (32*q+29) (64*q+55) := by
  apply exclude_of_cert 122 q 12 hq
  decide

/-- The full q>=21 necessary parameter reduction now retains
at most ten of the 128 residue classes of the 29-mod32 feeder. -/
theorem rooted_29_q_ten_mod128 (q : Nat) (hq : 21≤q)
    (hroot : Reach (32*q+29) (64*q+55)) :
    q%128=2 ∨ q%128=15 ∨ q%128=47 ∨ q%128=58 ∨
    q%128=63 ∨ q%128=74 ∨ q%128=79 ∨ q%128=82 ∨
    q%128=111 ∨ q%128=127 := by
  have h12 :=
    BB429Branch29Odd31.rooted_29_q_twelve_mod128 q hq hroot
  have h10 : q%128≠10 := by
    intro hh
    exact no_q_10_mod128 q hh hroot
  have h122 : q%128≠122 := by
    intro hh
    exact no_q_122_mod128 q hh hroot
  omega

#print axioms exclude_of_cert
#print axioms no_q_10_mod128
#print axioms no_q_122_mod128
#print axioms rooted_29_q_ten_mod128
end BB429Branch29Reflect
