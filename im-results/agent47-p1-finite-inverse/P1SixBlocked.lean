import P1SixAffine
import ConeKernel
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace BB6.Agent47P1
open BB6.Agent4Cone
open BB6.P1Reduction

/-- The deepest hub's full finite inverse cone closes under a single gap. -/
theorem sixb2_blocked (u:Nat) (hu:3≤u)
    (hgap:∀j:Nat,18*u+24 ≠14*2^j) :
    Blocked (sixb2 u) (sixb2d u) := by
  apply Blocked.feeder
  · dsimp [sixb2]; omega
  · dsimp [sixb2]; omega
  · dsimp [sixb2d]; omega
  · intro k hk
    have hs := sixb2_cases u k 1 hu hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h | h
    · have hc := (Prod.mk.inj h).2
      omega
    · have hc := (Prod.mk.inj h).2
      omega
  · intro k c hanc hc
    have hs := sixb2_cases u k c hu hanc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h | h
    · obtain ⟨hk,hc'⟩ := Prod.mk.inj h
      have hx : 2*k-4=4*u-6 := by omega
      have hy : c+4=28*u+39 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · obtain ⟨hk,hc'⟩ := Prod.mk.inj h
      have hx : 2*k-4=18*u+12 := by omega
      have hy : c+4=14*u+20 := by omega
      rw [hx,hy]
      exact Blocked.powerLeaf _ _ (by omega) (by omega) (by omega)
        (by intro j; have := hgap j; omega)

theorem sixb1_blocked (u:Nat) (hu:3≤u)
    (hgap1:∀j:Nat,20*u+28 ≠14*2^j)
    (hgap2:∀j:Nat,18*u+24 ≠14*2^j) :
    Blocked (sixb1 u) (sixb1d u) := by
  apply Blocked.feeder
  · dsimp [sixb1]; omega
  · dsimp [sixb1]; omega
  · dsimp [sixb1d]; omega
  · intro k hk
    have hs := sixb1_cases u k 1 hu hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h | h
    · have hc := (Prod.mk.inj h).2
      omega
    · have hc := (Prod.mk.inj h).2
      omega
  · intro k c hanc hc
    have hs := sixb1_cases u k c hu hanc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h | h
    · obtain ⟨hk,hc'⟩ := Prod.mk.inj h
      have hx : 2*k-4=sixb2 u := by dsimp [sixb2]; omega
      have hy : c+4=sixb2d u := by dsimp [sixb2d]; omega
      rw [hx,hy]
      exact sixb2_blocked u hu hgap2
    · obtain ⟨hk,hc'⟩ := Prod.mk.inj h
      have hx : 2*k-4=20*u+16 := by omega
      have hy : c+4=12*u+18 := by omega
      rw [hx,hy]
      exact Blocked.powerLeaf _ _ (by omega) (by omega) (by omega)
        (by intro j; have := hgap1 j; omega)

theorem sixroot_blocked (u:Nat) (hu:3≤u)
    (hgap0:∀j:Nat,30*u+40 ≠14*2^j)
    (hgap1:∀j:Nat,20*u+28 ≠14*2^j)
    (hgap2:∀j:Nat,18*u+24 ≠14*2^j) :
    Blocked (sixb0 u) (sixb0d u) := by
  apply Blocked.feeder
  · dsimp [sixb0]; omega
  · dsimp [sixb0]; omega
  · dsimp [sixb0d]; omega
  · intro k hk
    have hs := sixb0_cases u k 1 hu hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h | h | h | h
    all_goals have hc := (Prod.mk.inj h).2; omega
  · intro k c hanc hc
    have hs := sixb0_cases u k c hu hanc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h | h | h | h
    · obtain ⟨hk,hc'⟩ := Prod.mk.inj h
      have hx : 2*k-4=sixb1 u := by dsimp [sixb1]; omega
      have hy : c+4=sixb1d u := by dsimp [sixb1d]; omega
      rw [hx,hy]
      exact sixb1_blocked u hu hgap1 hgap2
    · obtain ⟨hk,hc'⟩ := Prod.mk.inj h
      have hx : 2*k-4=24*u+22 := by omega
      have hy : c+4=8*u+13 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · obtain ⟨hk,hc'⟩ := Prod.mk.inj h
      have hx : 2*k-4=28*u+26 := by omega
      have hy : c+4=4*u+7 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · obtain ⟨hk,hc'⟩ := Prod.mk.inj h
      have hx : 2*k-4=30*u+28 := by omega
      have hy : c+4=2*u+4 := by omega
      rw [hx,hy]
      exact Blocked.powerLeaf _ _ (by omega) (by omega) (by omega)
        (by intro j; have := hgap0 j; omega)

#print axioms sixroot_blocked
end BB6.Agent47P1
