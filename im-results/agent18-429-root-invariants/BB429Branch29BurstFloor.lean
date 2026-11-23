import BB429InverseKernel
import BB429Reset31
import Lean.Elab.Tactic.Omega

/-!
# A source-local all-time final-burst floor for #429's 29 (mod 32) reset feeder

The exact last-reset equation, in the coordinates
  u = 32*q + 29, w = 64*q + 55,
is 128*q + 3*n + 131 = 3*2^(n+2).
For n>=18 the right side is divisible by 524288; this forces
n=127+128*k and q=4092-3*k modulo4096 for every 0<=k<126.
The existing all-parameter, source-sound inverse-tree certificate
excludes each of these 126 affine cylinders. The first unexcluded
congruence candidate is n=16255, not a claimed attainable event.

The finite Boolean proof is checked by the Lean kernel with `decide`,
and BB429Kernel.cert_sound lifts the conclusion to every parameter.
No sampled finite orbit and no hypothesis on the size of q is used.
This is a NECESSARY condition for the final reset, not a halt decision.
-/

namespace BB429Branch29BurstFloor
open BB429Reset31
set_option maxHeartbeats 50000000
set_option maxRecDepth 30000

private def candidates : List Nat := List.range 126

/-- One finite certificate for all short-burst 2-adic candidates.
    Each predicate is a sound all-parameter inverse certificate, not
    an experiment on a particular large machine counter. -/
theorem short_candidates_cert :
    candidates.all (fun k =>
      BB429Kernel.cert 17
        ⟨131072, 32*(4092-3*k)+29, 262144, 64*(4092-3*k)+55⟩) = true := by
  decide

/-- Any authentic blank-root 29 (mod 32) odd-reset prestate with the
    exact branch-7 terminal-burst equation has final-burst length
    at least 16255. -/
theorem rooted_branch29_final_burst_floor
    (q n : Nat)
    (hn : 18 ≤ n)
    (hroot : Reach (32*q+29) (64*q+55))
    (heq : 128*q+3*n+131=3*2^(n+2)) :
    16255 ≤ n := by
  by_contra hshort
  have hshort' : n < 16255 := by omega
  have hpow : 2^(n+2)=524288*2^(n-17) := by
    have hsplit : n+2=19+(n-17) := by omega
    rw [hsplit, Nat.pow_add]
    norm_num
  have hmod : (128*q+3*n+131)%524288=0 := by
    rw [heq,hpow]
    omega
  let k := n/128
  have hnr : n%128=127 := by omega
  have hnform : n=128*k+127 := by dsimp [k]; omega
  have hk : k<126 := by omega
  have hqmod : q%4096=4092-3*k := by omega
  let s : BB429Kernel.Affine :=
    ⟨131072,32*(4092-3*k)+29,262144,64*(4092-3*k)+55⟩
  have hcert : BB429Kernel.cert 17 s = true := by
    exact (List.all_eq_true.mp short_candidates_cert) k
      (List.mem_range.mpr hk)
  have hx : BB429Kernel.va s (q/4096)=32*q+29 := by
    dsimp [s, BB429Kernel.va]
    omega
  have hy : BB429Kernel.vb s (q/4096)=64*q+55 := by
    dsimp [s, BB429Kernel.vb]
    omega
  have hsource : BB429NewResidue.Reach
      (BB429Kernel.va s (q/4096))
      (BB429Kernel.vb s (q/4096)) := by
    obtain ⟨i,hi⟩ := hroot
    exact ⟨i, by simpa only [hx,hy] using hi⟩
  exact (BB429Kernel.cert_sound 17 s (q/4096) hcert) hsource

#print axioms short_candidates_cert
#print axioms rooted_branch29_final_burst_floor
end BB429Branch29BurstFloor
