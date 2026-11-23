import BB429Branch29Reflect
import Lean.Elab.Tactic.Omega

/-!
# Uniform 58 affine inverse-tree exclusions in #429's 29mod32 feeder

The existing sound Agent33 affine backward kernel is instantiated at
parameter modulus 1024. The *single* kernel-reduced certificate proves
58 complete congruence cylinders unreachable for every q; combining
with exact earlier rooted 12-class restriction retains 38 q-cylinders
out of 1024. This is not evidence for termination of the blank orbit
and not a proof that any of the 38 surviving classes are reachable.
-/

namespace BB429Branch29Reflect1024
open BB429Reset31
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

def blocked1024 : List Nat :=
  [10,58,74,122,130,138,143,175,207,210,250,266,271,303,314,330,335,367,378,394,431,442,463,466,506,511,514,522,527,559,586,591,594,623,634,650,687,698,703,719,722,751,762,770,778,783,815,842,847,890,898,906,943,959,975,978,1007,1018]

def surviving1024 : List Nat :=
  [2,15,47,63,79,82,111,127,186,191,202,239,255,258,319,338,383,386,399,447,458,495,570,575,639,642,655,714,767,826,831,850,879,895,911,954,970,1023]

def prior128 : List Nat :=
  [2,10,15,47,58,63,74,79,82,111,122,127]

theorem blocked1024_nodup : blocked1024.Nodup := by decide
theorem blocked1024_count : blocked1024.length = 58 := by decide
theorem surviving1024_count : surviving1024.length = 38 := by decide

/-- Uniform (not finite-q sampling) certificate for the entire
parameter interval lattice represented by all blocked residues. -/
theorem blocked1024_cert :
    blocked1024.all (fun r =>
      BB429Kernel.cert 13 ⟨32768,32*r+29,65536,64*r+55⟩) = true := by
  decide

theorem no_blocked_residue (q r : Nat)
    (hr : q%1024=r)
    (hmem : r∈blocked1024) :
    ¬Reach (32*q+29) (64*q+55) := by
  intro hroot
  let t := q/1024
  have hq : q=1024*t+r := by dsimp [t]; omega
  have hx :
      BB429Kernel.va ⟨32768,32*r+29,65536,64*r+55⟩ t =
      32*q+29 := by
    simp only [BB429Kernel.va]
    omega
  have hy :
      BB429Kernel.vb ⟨32768,32*r+29,65536,64*r+55⟩ t =
      64*q+55 := by
    simp only [BB429Kernel.vb]
    omega
  obtain ⟨n,hn⟩ := hroot
  have hs : BB429NewResidue.Reach
      (BB429Kernel.va ⟨32768,32*r+29,65536,64*r+55⟩ t)
      (BB429Kernel.vb ⟨32768,32*r+29,65536,64*r+55⟩ t) :=
    ⟨n, by simpa only [hx,hy] using hn⟩
  have hc : BB429Kernel.cert 13
      ⟨32768,32*r+29,65536,64*r+55⟩ = true :=
    (List.all_eq_true.mp blocked1024_cert) r hmem
  exact (BB429Kernel.cert_sound 13
    ⟨32768,32*r+29,65536,64*r+55⟩ t hc) hs

/-- The simple finite arithmetic partition behind the uniform theorem:
all the 96 q mod1024 representatives of the known 12 mod128 classes
are in the excluded58 or the remaining38; this proof is only about a
finite residue set, while exclusion of each complete cylinder is
the preceding quantified certified soundness theorem. -/
theorem partition1024 :
    (List.range 1024).all (fun r =>
      decide (r%128 ∈ prior128 →
         r∈blocked1024 ∨ r∈surviving1024)) = true := by
  decide

/-- Main uniform 38/1024 necessary root result for any q>=21. -/
theorem rooted_29_q_38_mod1024 (q : Nat) (hq : 21≤q)
    (hroot : Reach (32*q+29) (64*q+55)) :
    q%1024 ∈ surviving1024 := by
  have h12 := BB429Branch29Odd31.rooted_29_q_twelve_mod128 q hq hroot
  have hr_lt : q%1024<1024 := Nat.mod_lt q (by decide)
  have hpartition :=
    (List.all_eq_true.mp partition1024) (q%1024)
      (List.mem_range.mpr hr_lt)
  have hpart :
      (q%1024)%128∈prior128 →
        q%1024∈blocked1024 ∨ q%1024∈surviving1024 :=
      of_decide_eq_true hpartition
  have hres : (q%1024)%128 ∈ prior128 := by
    simp only [prior128,List.mem_cons,List.not_mem_nil]
    omega
  have hdisj := hpart hres
  rcases hdisj with hblocked | hsurvivor
  · exact False.elim (no_blocked_residue q (q%1024) rfl hblocked hroot)
  · exact hsurvivor

#print axioms blocked1024_cert
#print axioms no_blocked_residue
#print axioms rooted_29_q_38_mod1024
end BB429Branch29Reflect1024
