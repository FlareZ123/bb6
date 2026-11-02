import P1R54Generated
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace BB6.Agent47P1
open BB6.P1Reduction

def sixb0 (u:Nat):Nat := 32*u+36
def sixb0d (u:Nat):Nat := 0*u+3
theorem sixb0_0 (u:Nat) (hu:3≤u) : inverseAt (sixb0 u) (sixb0d u) 0 =
    some (8*u+8, 16*u+21) := by
  have hb : 4 ≤ 32*u+36 ∧ (32*u+36)%4=0 := by omega
  simp [inverseAt,sixb0,sixb0d,hb]
  omega

theorem sixb0_1 (u:Nat) (hu:3≤u) : inverseAt (sixb0 u) (sixb0d u) 1 =
    some (12*u+13, 8*u+9) := by
  exact inverseAt_next_exact (sixb0 u) (sixb0d u) 0
    (8*u+8) (16*u+21)
    (12*u+13) (8*u+9) (sixb0_0 u hu)
    (by omega) (by omega) (by omega) (by omega)

theorem sixb0_2 (u:Nat) (hu:3≤u) : inverseAt (sixb0 u) (sixb0d u) 2 =
    some (14*u+15, 4*u+3) := by
  exact inverseAt_next_exact (sixb0 u) (sixb0d u) 1
    (12*u+13) (8*u+9)
    (14*u+15) (4*u+3) (sixb0_1 u hu)
    (by omega) (by omega) (by omega) (by omega)

theorem sixb0_3 (u:Nat) (hu:3≤u) : inverseAt (sixb0 u) (sixb0d u) 3 =
    some (15*u+16, 2*u+0) := by
  exact inverseAt_next_exact (sixb0 u) (sixb0d u) 2
    (14*u+15) (4*u+3)
    (15*u+16) (2*u+0) (sixb0_2 u hu)
    (by omega) (by omega) (by omega) (by omega)

theorem sixb0_shift_mod (u:Nat) (hu:3≤u) :
    ((sixb0d u)+(sixb0 u)/2+3)%16=8 := by
  simp [sixb0,sixb0d]
  omega

theorem sixb0_cases (u k c:Nat) (hu:3≤u)
    (h:GAncestor (sixb0 u) (sixb0d u) k c) :
    (k,c) ∈ [(8*u+8, 16*u+21), (12*u+13, 8*u+9), (14*u+15, 4*u+3), (15*u+16, 2*u+0)] := by
  have hn : ((sixb0d u)+(sixb0 u)/2+3)%16≠0 := by
    rw [sixb0_shift_mod u hu]
    decide
  obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (sixb0 u) (sixb0d u) k c 3 h hn
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · subst t
    rw [sixb0_0 u hu] at hval
    have hp : (k,c) = (8*u+8, 16*u+21) := (Option.some.inj hval).symm
    simp [hp]
  · subst t
    rw [sixb0_1 u hu] at hval
    have hp : (k,c) = (12*u+13, 8*u+9) := (Option.some.inj hval).symm
    simp [hp]
  · subst t
    rw [sixb0_2 u hu] at hval
    have hp : (k,c) = (14*u+15, 4*u+3) := (Option.some.inj hval).symm
    simp [hp]
  · subst t
    rw [sixb0_3 u hu] at hval
    have hp : (k,c) = (15*u+16, 2*u+0) := (Option.some.inj hval).symm
    simp [hp]

def sixb1 (u:Nat):Nat := 16*u+12
def sixb1d (u:Nat):Nat := 16*u+25
theorem sixb1_0 (u:Nat) (hu:3≤u) : inverseAt (sixb1 u) (sixb1d u) 0 =
    some (4*u+2, 24*u+31) := by
  have hb : 4 ≤ 16*u+12 ∧ (16*u+12)%4=0 := by omega
  simp [inverseAt,sixb1,sixb1d,hb]
  omega

theorem sixb1_1 (u:Nat) (hu:3≤u) : inverseAt (sixb1 u) (sixb1d u) 1 =
    some (10*u+10, 12*u+14) := by
  exact inverseAt_next_exact (sixb1 u) (sixb1d u) 0
    (4*u+2) (24*u+31)
    (10*u+10) (12*u+14) (sixb1_0 u hu)
    (by omega) (by omega) (by omega) (by omega)

theorem sixb1_shift_mod (u:Nat) (hu:3≤u) :
    ((sixb1d u)+(sixb1 u)/2+3)%4=2 := by
  simp [sixb1,sixb1d]
  omega

theorem sixb1_cases (u k c:Nat) (hu:3≤u)
    (h:GAncestor (sixb1 u) (sixb1d u) k c) :
    (k,c) ∈ [(4*u+2, 24*u+31), (10*u+10, 12*u+14)] := by
  have hn : ((sixb1d u)+(sixb1 u)/2+3)%4≠0 := by
    rw [sixb1_shift_mod u hu]
    decide
  obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (sixb1 u) (sixb1d u) k c 1 h hn
  have hcases : t=0 ∨ t=1 := by omega
  rcases hcases with h0 | h1
  · subst t
    rw [sixb1_0 u hu] at hval
    have hp : (k,c) = (4*u+2, 24*u+31) := (Option.some.inj hval).symm
    simp [hp]
  · subst t
    rw [sixb1_1 u hu] at hval
    have hp : (k,c) = (10*u+10, 12*u+14) := (Option.some.inj hval).symm
    simp [hp]

def sixb2 (u:Nat):Nat := 8*u
def sixb2d (u:Nat):Nat := 24*u+35
theorem sixb2_0 (u:Nat) (hu:3≤u) : inverseAt (sixb2 u) (sixb2d u) 0 =
    some (2*u-1, 28*u+35) := by
  have hb : 4 ≤ sixb2 u ∧ (sixb2 u)%4=0 := by dsimp [sixb2]; omega
  simp only [inverseAt]
  rw [if_pos hb]
  simp only [sixb2, sixb2d]
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor <;> omega

theorem sixb2_1 (u:Nat) (hu:3≤u) : inverseAt (sixb2 u) (sixb2d u) 1 =
    some (9*u+8, 14*u+16) := by
  exact inverseAt_next_exact (sixb2 u) (sixb2d u) 0
    (2*u-1) (28*u+35)
    (9*u+8) (14*u+16) (sixb2_0 u hu)
    (by omega) (by omega) (by omega) (by omega)

theorem sixb2_shift_mod (u:Nat) (hu:3≤u) :
    ((sixb2d u)+(sixb2 u)/2+3)%4=2 := by
  simp [sixb2,sixb2d]
  omega

theorem sixb2_cases (u k c:Nat) (hu:3≤u)
    (h:GAncestor (sixb2 u) (sixb2d u) k c) :
    (k,c) ∈ [(2*u-1, 28*u+35), (9*u+8, 14*u+16)] := by
  have hn : ((sixb2d u)+(sixb2 u)/2+3)%4≠0 := by
    rw [sixb2_shift_mod u hu]
    decide
  obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (sixb2 u) (sixb2d u) k c 1 h hn
  have hcases : t=0 ∨ t=1 := by omega
  rcases hcases with h0 | h1
  · subst t
    rw [sixb2_0 u hu] at hval
    have hp : (k,c) = (2*u-1, 28*u+35) := (Option.some.inj hval).symm
    simp [hp]
  · subst t
    rw [sixb2_1 u hu] at hval
    have hp : (k,c) = (9*u+8, 14*u+16) := (Option.some.inj hval).symm
    simp [hp]

end BB6.Agent47P1
