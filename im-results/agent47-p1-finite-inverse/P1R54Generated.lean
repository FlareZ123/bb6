import P1InverseFixed
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace BB6.Agent47P1
open BB6.P1Reduction

/-- Exact next stage of the executable inversion algorithm. -/
theorem inverseAt_next_exact (b d t k c k2 c2 : Nat)
    (h : inverseAt b d t = some (k,c))
    (hc : 3 ≤ c) (hodd : c%2=1)
    (hk : k+(c-3)/2/2+1=k2) (hcc : (c-3)/2=c2) :
    inverseAt b d (t+1) = some (k2,c2) := by
  calc
    inverseAt b d (t+1) = some (k+(c-3)/2/2+1,(c-3)/2) :=
      by simp [inverseAt,h,hc,hodd]
    _ = some (k2,c2) := by rw [hk, hcc]

def r54b0 (s:Nat):Nat := 131072*s+130948
def r54b0d (s:Nat):Nat := 0*s+3
theorem r54b0_0 (s:Nat) : inverseAt (r54b0 s) (r54b0d s) 0 =
    some (32768*s+32736, 65536*s+65477) := by
  simp [inverseAt,r54b0,r54b0d]
  omega

theorem r54b0_1 (s:Nat) : inverseAt (r54b0 s) (r54b0d s) 1 =
    some (49152*s+49105, 32768*s+32737) := by
  exact inverseAt_next_exact (r54b0 s) (r54b0d s) 0
    (32768*s+32736) (65536*s+65477)
    (49152*s+49105) (32768*s+32737) (r54b0_0 s)
    (by omega) (by omega) (by omega) (by omega)

theorem r54b0_2 (s:Nat) : inverseAt (r54b0 s) (r54b0d s) 2 =
    some (57344*s+57289, 16384*s+16367) := by
  exact inverseAt_next_exact (r54b0 s) (r54b0d s) 1
    (49152*s+49105) (32768*s+32737)
    (57344*s+57289) (16384*s+16367) (r54b0_1 s)
    (by omega) (by omega) (by omega) (by omega)

theorem r54b0_3 (s:Nat) : inverseAt (r54b0 s) (r54b0d s) 3 =
    some (61440*s+61381, 8192*s+8182) := by
  exact inverseAt_next_exact (r54b0 s) (r54b0d s) 2
    (57344*s+57289) (16384*s+16367)
    (61440*s+61381) (8192*s+8182) (r54b0_2 s)
    (by omega) (by omega) (by omega) (by omega)

theorem r54b0_shift_mod (s:Nat) :
    ((r54b0d s)+(r54b0 s)/2+3)%16=8 := by
  simp [r54b0,r54b0d]
  omega

theorem r54b0_cases (s k c:Nat)
    (h:GAncestor (r54b0 s) (r54b0d s) k c) :
    (k,c) ∈ [(32768*s+32736, 65536*s+65477), (49152*s+49105, 32768*s+32737), (57344*s+57289, 16384*s+16367), (61440*s+61381, 8192*s+8182)] := by
  have hn : ((r54b0d s)+(r54b0 s)/2+3)%16≠0 := by
    rw [r54b0_shift_mod]
    decide
  obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (r54b0 s) (r54b0d s) k c 3 h hn
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases hcases with h0|h1|h2|h3
  · subst t
    rw [r54b0_0] at hval
    have hp : (k,c) = (32768*s+32736, 65536*s+65477) := (Option.some.inj hval).symm
    simp [hp]
  · subst t
    rw [r54b0_1] at hval
    have hp : (k,c) = (49152*s+49105, 32768*s+32737) := (Option.some.inj hval).symm
    simp [hp]
  · subst t
    rw [r54b0_2] at hval
    have hp : (k,c) = (57344*s+57289, 16384*s+16367) := (Option.some.inj hval).symm
    simp [hp]
  · subst t
    rw [r54b0_3] at hval
    have hp : (k,c) = (61440*s+61381, 8192*s+8182) := (Option.some.inj hval).symm
    simp [hp]

def r54b1 (s:Nat):Nat := 65536*s+65468
def r54b1d (s:Nat):Nat := 65536*s+65481
theorem r54b1_0 (s:Nat) : inverseAt (r54b1 s) (r54b1d s) 0 =
    some (16384*s+16366, 98304*s+98215) := by
  simp [inverseAt,r54b1,r54b1d]
  omega

theorem r54b1_1 (s:Nat) : inverseAt (r54b1 s) (r54b1d s) 1 =
    some (40960*s+40920, 49152*s+49106) := by
  exact inverseAt_next_exact (r54b1 s) (r54b1d s) 0
    (16384*s+16366) (98304*s+98215)
    (40960*s+40920) (49152*s+49106) (r54b1_0 s)
    (by omega) (by omega) (by omega) (by omega)

theorem r54b1_shift_mod (s:Nat) :
    ((r54b1d s)+(r54b1 s)/2+3)%4=2 := by
  simp [r54b1,r54b1d]
  omega

theorem r54b1_cases (s k c:Nat)
    (h:GAncestor (r54b1 s) (r54b1d s) k c) :
    (k,c) ∈ [(16384*s+16366, 98304*s+98215), (40960*s+40920, 49152*s+49106)] := by
  have hn : ((r54b1d s)+(r54b1 s)/2+3)%4≠0 := by
    rw [r54b1_shift_mod]
    decide
  obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (r54b1 s) (r54b1d s) k c 1 h hn
  have hcases : t=0 ∨ t=1 := by omega
  rcases hcases with h0|h1
  · subst t
    rw [r54b1_0] at hval
    have hp : (k,c) = (16384*s+16366, 98304*s+98215) := (Option.some.inj hval).symm
    simp [hp]
  · subst t
    rw [r54b1_1] at hval
    have hp : (k,c) = (40960*s+40920, 49152*s+49106) := (Option.some.inj hval).symm
    simp [hp]

def r54b2 (s:Nat):Nat := 32768*s+32728
def r54b2d (s:Nat):Nat := 98304*s+98219
theorem r54b2_0 (s:Nat) : inverseAt (r54b2 s) (r54b2d s) 0 =
    some (8192*s+8181, 114688*s+114583) := by
  simp [inverseAt,r54b2,r54b2d]
  omega

theorem r54b2_1 (s:Nat) : inverseAt (r54b2 s) (r54b2d s) 1 =
    some (36864*s+36827, 57344*s+57290) := by
  exact inverseAt_next_exact (r54b2 s) (r54b2d s) 0
    (8192*s+8181) (114688*s+114583)
    (36864*s+36827) (57344*s+57290) (r54b2_0 s)
    (by omega) (by omega) (by omega) (by omega)

theorem r54b2_shift_mod (s:Nat) :
    ((r54b2d s)+(r54b2 s)/2+3)%4=2 := by
  simp [r54b2,r54b2d]
  omega

theorem r54b2_cases (s k c:Nat)
    (h:GAncestor (r54b2 s) (r54b2d s) k c) :
    (k,c) ∈ [(8192*s+8181, 114688*s+114583), (36864*s+36827, 57344*s+57290)] := by
  have hn : ((r54b2d s)+(r54b2 s)/2+3)%4≠0 := by
    rw [r54b2_shift_mod]
    decide
  obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (r54b2 s) (r54b2d s) k c 1 h hn
  have hcases : t=0 ∨ t=1 := by omega
  rcases hcases with h0|h1
  · subst t
    rw [r54b2_0] at hval
    have hp : (k,c) = (8192*s+8181, 114688*s+114583) := (Option.some.inj hval).symm
    simp [hp]
  · subst t
    rw [r54b2_1] at hval
    have hp : (k,c) = (36864*s+36827, 57344*s+57290) := (Option.some.inj hval).symm
    simp [hp]

end BB6.Agent47P1
