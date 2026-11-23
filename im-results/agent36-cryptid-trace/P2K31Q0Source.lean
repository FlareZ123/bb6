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


/-- The second previously untreated q=0 terminal cylinder:
    k = 81*s+16.  Here the exact guarded phase is reset, E, B, E,
    reaching the same Y3 E/p0,q=3 regularizing terminal. -/
def k16 (s : Nat) : Nat := 81*s+16
def k16E1 (s : Nat) : Nat := 216*s+43
def k16B (s : Nat) : Nat := 576*s+117
def k16E2 (s : Nat) : Nat := 1536*s+314
def k16Terminal (s : Nat) : Nat := 4096*s+839

def prefixT16 (s : Nat) : Nat :=
  eTwoTime (k16 s) 0 +
    (eT (k16E1 s) 0 + (bT (k16B s) + eT (k16E2 s) 1))

theorem prefix16_to_e_zero (s : Nat) :
    run (prefixT16 s)
      (packet (3*k16 s+4) 0 2 (false::List.replicate 6 true)) =
      packet (3*k16Terminal s+4) 3 0 marker := by
  have h1 : 8*k16 s+5=3*k16E1 s+4 := by
    simp [k16,k16E1]; omega
  have h2 : 8*k16E1 s+9=3*k16B s+2 := by
    simp [k16E1,k16B]; omega
  have h3 : 8*k16B s+10=3*k16E2 s+4 := by
    simp [k16B,k16E2]; omega
  have h4 : 8*k16E2 s+9=3*k16Terminal s+4 := by
    simp [k16E2,k16Terminal]; omega
  have he1 :
      run (eT (k16E1 s) 0)
        (packet (3*k16E1 s+4) 0 6 marker) =
        packet (8*k16E1 s+9) 2 3 marker := by
    simpa [eT] using (e_packet (k16E1 s) 0 3 marker)
  have hb :
      run (bT (k16B s))
        (packet (3*k16B s+2) 2 3 marker) =
        packet (8*k16B s+10) 1 3 marker := by
    simpa [bT] using (b_packet (k16B s) 1 3 marker)
  have he2 :
      run (eT (k16E2 s) 1)
        (packet (3*k16E2 s+4) 1 3 marker) =
        packet (8*k16E2 s+9) 3 0 marker := by
    simpa [eT] using (e_packet (k16E2 s) 1 0 marker)
  unfold prefixT16
  rw [run_add,e_two_reset,h1]
  change run (eT (k16E1 s) 0 + (bT (k16B s) + eT (k16E2 s) 1))
    (packet (3*k16E1 s+4) 0 6 marker) = _
  rw [run_add,he1,h2,run_add,hb,h3,he2,h4]

/-- Every k≡16 (mod81), q=0 fixed-tail exceptional packet regularizes. -/
theorem k16_q0_regular (s : Nat) :
    ∃ T a q b,
      BB6.BoundaryPadding.ObsEq
        (run T
          (packet (3*k16 s+4) 0 2
            (false::List.replicate 6 true)))
        (BB6.Agent2BoundaryBZero.regularSection a q b) := by
  obtain ⟨Tr,a,q,b,hreg⟩ :=
    BB6.Agent2MarkerTower.e_zero_q0_regular (k16Terminal s) 1 2
  refine ⟨prefixT16 s+Tr,a,q,b,?_⟩
  rw [run_add,prefix16_to_e_zero]
  have hm : marker = BB6.Agent2MarkerTower.marker 3 := by decide
  rw [hm]
  exact hreg

/-- The union of the two new full linear k-cylinders for q=0. -/
theorem k16_or_k31_q0_regular (k : Nat)
    (h : (∃ s, k = k16 s) ∨ (∃ s, k = k0 s)) :
    ∃ T a q b,
      BB6.BoundaryPadding.ObsEq
        (run T (packet (3*k+4) 0 2 (false::List.replicate 6 true)))
        (BB6.Agent2BoundaryBZero.regularSection a q b) := by
  rcases h with ⟨s,hs⟩ | ⟨s,hs⟩
  · rw [hs]
    exact k16_q0_regular s
  · rw [hs]
    exact k31_q0_regular s

#print axioms prefix16_to_e_zero
#print axioms k16_q0_regular
#print axioms k16_or_k31_q0_regular

#print axioms prefix_to_e_zero
#print axioms k31_q0_regular
end BB6.Agent36K31
