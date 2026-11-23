import Lean.Elab.Tactic.Omega
import PacketP2ResetSource
import MarkerTowerSource

/-!
  New k = 81*s + 31, Q=0 fixed-tail E/p=2 reset family.  This
  corridor is not among the previously certified k=27*s+22
  or k=27*s+25 source families, and needs no unproved root prefix.

  Exact original-machine source path:
    E/p2 reset; E; E; B; E/p0 zero-run with Y_3=(01)^3 11.
  The E/p0 terminal has q=3, so the general all-q-divisible-by-3
  source theorem closes the path to a regular F0 section.
-/

namespace BB6.Agent36K31

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2PacketP2Reset

set_option maxHeartbeats 14000000
set_option maxRecDepth 8192

def k0 (s : Nat) : Nat := 81*s+31
def k1 (s : Nat) : Nat := 216*s+83
def k2 (s : Nat) : Nat := 576*s+223
def kB (s : Nat) : Nat := 1536*s+597
def kE (s : Nat) : Nat := 4096*s+1594

def eT (x q : Nat) : Nat := 12*x*x+49*x+58+6*q
def bT (x : Nat) : Nat := 12*x*x+49*x+40
def prefixT (s : Nat) : Nat :=
  eTwoTime (k0 s) 0 + (eT (k1 s) 0 + (eT (k2 s) 2 + bT (kB s)))

/-- Exact original-machine E-reset, two E packets, and B packet,
    reaching E with q=3,p=0 and unchanged Y3 marker. -/
theorem prefix_to_e_zero (s : Nat) :
    run (prefixT s)
      (packet (3*k0 s+4) 0 2 (false::List.replicate 6 true)) =
      packet (3*kE s+4) 3 0 marker := by
  have h1 : 8*k0 s+5=3*k1 s+4 := by simp [k0,k1]; omega
  have h2 : 8*k1 s+9=3*k2 s+4 := by simp [k1,k2]; omega
  have h3 : 8*k2 s+9=3*kB s+2 := by simp [k2,kB]; omega
  have h4 : 8*kB s+10=3*kE s+4 := by simp [kB,kE]; omega
  have he1 :
      run (eT (k1 s) 0)
        (packet (3*k1 s+4) 0 6 marker) =
        packet (8*k1 s+9) 2 3 marker := by
    simpa [eT] using
      (e_packet (k1 s) 0 3 marker)
  have he2 :
      run (eT (k2 s) 2)
        (packet (3*k2 s+4) 2 3 marker) =
        packet (8*k2 s+9) 4 0 marker := by
    simpa [eT] using
      (e_packet (k2 s) 2 0 marker)
  have hb :
      run (bT (kB s))
        (packet (3*kB s+2) 4 0 marker) =
        packet (8*kB s+10) 3 0 marker := by
    simpa [bT] using
      (b_packet (kB s) 3 0 marker)
  unfold prefixT
  rw [run_add, e_two_reset, h1]
  change run (eT (k1 s) 0 + (eT (k2 s) 2 + bT (kB s)))
    (packet (3*k1 s+4) 0 6 marker) = _
  rw [run_add,he1,h2,run_add,he2,h3,hb,h4]

/-- Infinite q=0 original-machine E/p2 family in the previously untreated
    k ≡ 31 (mod 81) residue class, returned to the physical canonical L.
    No claim that the true blank-root orbit reaches the family is made. -/
theorem k31_q0_regular (s : Nat) :
    ∃ T a q b,
      BB6.BoundaryPadding.ObsEq
        (run T
          (packet (3*k0 s+4) 0 2
            (false::List.replicate 6 true)))
        (BB6.Agent2BoundaryBZero.regularSection a q b) := by
  obtain ⟨Tr,a,q,b,hreg⟩ :=
    BB6.Agent2MarkerTower.e_zero_q0_regular (kE s) 1 2
  refine ⟨prefixT s+Tr,a,q,b,?_⟩
  rw [run_add,prefix_to_e_zero]
  have hm : marker = BB6.Agent2MarkerTower.marker 3 := by decide
  rw [hm]
  exact hreg

#print axioms prefix_to_e_zero
#print axioms k31_q0_regular
end BB6.Agent36K31
