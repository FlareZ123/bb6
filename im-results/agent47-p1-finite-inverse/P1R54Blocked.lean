import P1R54Generated
import ConeKernel
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace BB6.Agent47P1
open BB6.Agent4Cone
open BB6.P1Reduction

theorem r54b2_blocked (s:Nat) (hgap:∀j:Nat,73728*s+73662 ≠ 14*2^j) :
    Blocked (r54b2 s) (r54b2d s) := by
  apply Blocked.feeder
  · dsimp [r54b2]; omega
  · dsimp [r54b2]; omega
  · dsimp [r54b2d]; omega
  · intro k hk
    have hs := r54b2_cases s k 1 hk
    simp only [List.mem_cons] at hs
    simp only [List.not_mem_nil, or_false] at hs
    rcases hs with h | h
    · have hc := (Prod.mk.inj h).2
      omega
    · have hc := (Prod.mk.inj h).2
      omega
  · intro k c hanc hc
    have hs := r54b2_cases s k c hanc
    simp only [List.mem_cons] at hs
    simp only [List.not_mem_nil, or_false] at hs
    rcases hs with h | h
    · obtain ⟨hk,hc'⟩ := Prod.mk.inj h
      have hx : 2*k-4=16384*s+16358 := by omega
      have hy : c+4=114688*s+114587 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · obtain ⟨hk,hc'⟩ := Prod.mk.inj h
      have hx : 2*k-4=73728*s+73650 := by omega
      have hy : c+4=57344*s+57294 := by omega
      rw [hx,hy]
      exact Blocked.powerLeaf _ _ (by omega) (by omega) (by omega)
        (by intro j; have := hgap j; omega)

/-- Middle-level complete symbolic inverse certificate. -/
theorem r54b1_blocked (s:Nat)
    (hgap1:∀j:Nat,81920*s+81848 ≠ 14*2^j)
    (hgap2:∀j:Nat,73728*s+73662 ≠ 14*2^j) :
    Blocked (r54b1 s) (r54b1d s) := by
  apply Blocked.feeder
  · dsimp [r54b1]; omega
  · dsimp [r54b1]; omega
  · dsimp [r54b1d]; omega
  · intro k hk
    have hs := r54b1_cases s k 1 hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h | h
    · have hc := (Prod.mk.inj h).2
      omega
    · have hc := (Prod.mk.inj h).2
      omega
  · intro k c hanc hc
    have hs := r54b1_cases s k c hanc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h | h
    · obtain ⟨hk,hc'⟩ := Prod.mk.inj h
      have hx : 2*k-4=r54b2 s := by dsimp [r54b2]; omega
      have hy : c+4=r54b2d s := by dsimp [r54b2d]; omega
      rw [hx,hy]
      exact r54b2_blocked s hgap2
    · obtain ⟨hk,hc'⟩ := Prod.mk.inj h
      have hx : 2*k-4=81920*s+81836 := by omega
      have hy : c+4=49152*s+49110 := by omega
      rw [hx,hy]
      exact Blocked.powerLeaf _ _ (by omega) (by omega) (by omega)
        (by intro j; have := hgap1 j; omega)

/-- Three-hub source-level cone certificate with three arithmetic power leaves.
The separate gap lemmas specialize s to the actual critical index family. -/
theorem r54root_blocked (s:Nat)
    (hgap0:∀j:Nat,122880*s+122770 ≠ 14*2^j)
    (hgap1:∀j:Nat,81920*s+81848 ≠ 14*2^j)
    (hgap2:∀j:Nat,73728*s+73662 ≠ 14*2^j) :
    Blocked (r54b0 s) (r54b0d s) := by
  apply Blocked.feeder
  · dsimp [r54b0]; omega
  · dsimp [r54b0]; omega
  · dsimp [r54b0d]; omega
  · intro k hk
    have hs := r54b0_cases s k 1 hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h | h | h | h
    all_goals have hc := (Prod.mk.inj h).2; omega
  · intro k c hanc hc
    have hs := r54b0_cases s k c hanc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h | h | h | h
    · obtain ⟨hk,hc'⟩ := Prod.mk.inj h
      have hx : 2*k-4=r54b1 s := by dsimp [r54b1]; omega
      have hy : c+4=r54b1d s := by dsimp [r54b1d]; omega
      rw [hx,hy]
      exact r54b1_blocked s hgap1 hgap2
    · obtain ⟨hk,hc'⟩ := Prod.mk.inj h
      have hx : 2*k-4=98304*s+98206 := by omega
      have hy : c+4=32768*s+32741 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · obtain ⟨hk,hc'⟩ := Prod.mk.inj h
      have hx : 2*k-4=114688*s+114574 := by omega
      have hy : c+4=16384*s+16371 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · obtain ⟨hk,hc'⟩ := Prod.mk.inj h
      have hx : 2*k-4=122880*s+122758 := by omega
      have hy : c+4=8192*s+8186 := by omega
      rw [hx,hy]
      exact Blocked.powerLeaf _ _ (by omega) (by omega) (by omega)
        (by intro j; have := hgap0 j; omega)

#print axioms r54root_blocked
#print axioms r54b2_blocked
end BB6.Agent47P1
