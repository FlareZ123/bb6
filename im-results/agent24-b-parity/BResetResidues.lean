import BParityAperiodic

namespace BB6.Agent24.Reset
open BB6.Agent24

/-- Exact reset recursion from Agent 18, copied without the original machine bridge. -/
def resetA : Nat → Nat
  | 0 => 3
  | n+1 =>
      let z := iterG (resetA n) 0
      z + 9 - 3*(z%2)

def sampleZ (n : Nat) : Nat := iterG (resetA n) 0

theorem iterG_succ (n : Nat) : iterG (n+1) 0 = G (iterG n 0) := by
  exact iterG_apply_G n 0

theorem G_mod3 (z : Nat) : G z %3 = (1+2*(z%2))%3 := by
  dsimp [G]
  omega

theorem G_mod3_small (z : Nat) : G z%3=0 ∨ G z%3=1 := by
  have h:=G_mod3 z
  have hb:=Nat.mod_lt z (by omega : 0<2)
  omega

theorem resetA_pos (n : Nat) : 1 ≤ resetA n := by
  cases n with
  | zero => decide
  | succ n =>
    dsimp [resetA]
    have hb := Nat.mod_lt (sampleZ n) (by omega : 0<2)
    dsimp [sampleZ] at hb
    omega

theorem resetA_odd (n : Nat) : resetA n%2=1 := by
  cases n with
  | zero => decide
  | succ n =>
    dsimp [resetA]
    have hb := Nat.mod_lt (iterG (resetA n) 0) (by omega : 0<2)
    omega

theorem resetA_mod3 (n : Nat) : resetA n%3=0 ∨ resetA n%3=1 := by
  cases n with
  | zero => decide
  | succ n =>
    have hpos := resetA_pos n
    obtain ⟨m, hm⟩ : ∃ m, resetA n = m+1 := by
      exact ⟨resetA n-1, by omega⟩
    have hz := G_mod3_small (iterG m 0)
    have hiter : iterG (resetA n) 0 = G (iterG m 0) := by rw [hm,iterG_succ]
    dsimp [resetA]
    rw [hiter]
    have hb := Nat.mod_lt (G (iterG m 0)) (by omega : 0<2)
    omega

theorem resetA_mod6 (n : Nat) : resetA n%6=1 ∨ resetA n%6=3 := by
  have hodd := resetA_odd n
  have h3 := resetA_mod3 n
  omega

theorem five_pow_add6 (n : Nat) : 5^(n+6)%7=5^n%7 := by
  rw [Nat.pow_add]
  have h : 5^6 = 15625 := by decide
  rw [h]
  omega

theorem five_pow_mod7 (n : Nat) : 5^n%7=5^(n%6)%7 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hsmall : n<6
    · have he : n%6=n := by omega
      rw [he]
    · have hn : n=n-6+6 := by omega
      have hlt : n-6<n := by omega
      have hm : (n-6)%6=n%6 := by omega
      calc
        5^n%7 = 5^((n-6)+6)%7 := congrArg (fun x : Nat => 5^x%7) hn
        _ = 5^(n-6)%7 := five_pow_add6 (n-6)
        _ = 5^((n-6)%6)%7 := ih (n-6) hlt
        _ = 5^(n%6)%7 := by rw [hm]

theorem sample_v_mod7 (n : Nat) :
    (sampleZ n+8)%7=5 ∨ (sampleZ n+8)%7=6 := by
  have hmod:=iterG_mod7 (resetA n)
  have hpow:=five_pow_mod7 (resetA n)
  have hpow8 : (8*5^(resetA n))%7=(8*5^(resetA n%6))%7 := by omega
  have h6:=resetA_mod6 n
  rcases h6 with h1|h3
  · rw [h1] at hpow8
    have he : (8*5^1)%7=5 := by decide
    left
    dsimp [sampleZ]
    omega
  · rw [h3] at hpow8
    have he : (8*5^3)%7=6 := by decide
    right
    dsimp [sampleZ]
    omega

/-- If an entire cycle survives its reset index is 3 or 4 modulo 7. -/
theorem odd_sample_reset_mod7 (n : Nat)
    (hs : sampleZ n%2=1) :
    resetA (n+1)%7=3 ∨ resetA (n+1)%7=4 := by
  have hm := sample_v_mod7 n
  have hzn := Nat.mod_lt (sampleZ n) (by omega : 0<2)
  dsimp [resetA, sampleZ] at *
  omega

/-- Conversely, if the sample is an even halting witness, the next synthetic
    reset index has residue 0 or 6 modulo 7. -/
theorem even_sample_reset_mod7 (n : Nat)
    (hs : sampleZ n%2=0) :
    resetA (n+1)%7=0 ∨ resetA (n+1)%7=6 := by
  have hm := sample_v_mod7 n
  have hzn := Nat.mod_lt (sampleZ n) (by omega : 0<2)
  dsimp [resetA, sampleZ] at *
  omega

/-- A completely arithmetic alternative characterization of the sampled parity bit. -/
theorem sample_odd_iff_reset_residue (n : Nat) :
    sampleZ n%2=1 ↔ (resetA (n+1)%7=3 ∨ resetA (n+1)%7=4) := by
  constructor
  · exact odd_sample_reset_mod7 n
  · intro hr
    by_cases hodd : sampleZ n%2=1
    · exact hodd
    · have hzero : sampleZ n%2=0 := by
        have hlt := Nat.mod_lt (sampleZ n) (by omega : 0<2)
        omega
      have heven := even_sample_reset_mod7 n hzero
      omega

theorem sample_even_iff_reset_residue (n : Nat) :
    sampleZ n%2=0 ↔ (resetA (n+1)%7=0 ∨ resetA (n+1)%7=6) := by
  constructor
  · exact even_sample_reset_mod7 n
  · intro hr
    by_cases heven : sampleZ n%2=0
    · exact heven
    · have hodd : sampleZ n%2=1 := by
        have hlt := Nat.mod_lt (sampleZ n) (by omega : 0<2)
        omega
      have hsurvive := odd_sample_reset_mod7 n hodd
      omega

/-- The parity at the *penultimate* scalar iteration determines which
    of the two possible modulo-six reset classes occurs. -/
theorem next_reset_mod6_iff_pre_even (n : Nat) :
    resetA (n+1)%6=1 ↔
      (iterG (resetA n-1) 0)%2=0 := by
  have hpos := resetA_pos n
  obtain ⟨m,hm⟩ : ∃ m, resetA n=m+1 :=
    ⟨resetA n-1, by omega⟩
  have hm' : resetA n-1=m := by omega
  have hstep : sampleZ n = G (iterG m 0) := by
    dsimp [sampleZ]
    rw [hm,iterG_succ]
  have hg := G_mod3 (iterG m 0)
  have hp := Nat.mod_lt (iterG m 0) (by omega : 0<2)
  have hq := Nat.mod_lt (sampleZ n) (by omega : 0<2)
  have hodd := resetA_odd (n+1)
  have h3 : resetA (n+1)%3 = sampleZ n%3 := by
    dsimp [resetA]
    omega
  rw [hstep] at h3
  rw [hm']
  constructor
  · intro he
    omega
  · intro he
    omega

theorem next_reset_mod6_iff_pre_odd (n : Nat) :
    resetA (n+1)%6=3 ↔
      (iterG (resetA n-1) 0)%2=1 := by
  have hh := next_reset_mod6_iff_pre_even n
  have ha := resetA_mod6 (n+1)
  have hb := Nat.mod_lt (iterG (resetA n-1) 0) (by omega : 0<2)
  omega

#print axioms next_reset_mod6_iff_pre_even
#print axioms next_reset_mod6_iff_pre_odd

#print axioms sample_odd_iff_reset_residue
#print axioms sample_even_iff_reset_residue
#print axioms odd_sample_reset_mod7
#print axioms even_sample_reset_mod7
end BB6.Agent24.Reset
