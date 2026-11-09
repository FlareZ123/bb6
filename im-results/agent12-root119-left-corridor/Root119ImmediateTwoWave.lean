import Root119TwoWaveRootPrefix
namespace BB6Root119

def immF1 (b : Conf) : Conf :=
  ⟨.F,b.h-1,twoWavePrefixTape b.tape b.h⟩
def immB1 (n : Nat) (b : Conf) : Conf :=
  ⟨.B,b.h-2,oddWaveTape n (immF1 b).tape (b.h-1)⟩
def immF2 (n : Nat) (b : Conf) : Conf :=
  ⟨.F,b.h-3,setBit (immB1 n b).tape (b.h-2) true⟩
def immB2 (n m : Nat) (b : Conf) : Conf :=
  ⟨.B,b.h-4,oddWaveTape m (immF2 n b).tape (b.h-3)⟩

/-- An immediate B/0 return after two right waves, without a later F/B retreat. -/
theorem imm_two_wave_exact (n m : Nat) (b : Conf)
    (hb : BZero b)
    (hl1 : b.tape (b.h-1) = true)
    (hl2 : b.tape (b.h-2) = false)
    (hl3 : b.tape (b.h-3) = true)
    (hw1 : (immF1 b).tape (b.h-1) = true)
    (hones1 : ∀ j : Nat, j < 2*n+1 →
      (immF1 b).tape (b.h-1+1+(j:Int)) = true)
    (hzero1 : (immF1 b).tape (b.h-1+2*(n:Int)+2) = false)
    (hb1 : (immB1 n b).tape (b.h-2) = true)
    (hw2 : (immF2 n b).tape (b.h-3) = true)
    (hones2 : ∀ j : Nat, j < 2*m+1 →
      (immF2 n b).tape (b.h-3+1+(j:Int)) = true)
    (hzero2 : (immF2 n b).tape (b.h-3+2*(m:Int)+2) = false) :
    run (4*n+4*m+20) b = some (immB2 n m b) := by
  have hp : run 9 b = some (immF1 b) := by
    simpa [immF1] using b0_two_wave_prefix b hb hl1 hl2 hl3
  have h1 : run (4*n+5) (immF1 b) = some (immB1 n b) := by
    simpa [immF1,immB1,show b.h-1-1 = b.h-2 by omega] using
      (odd_f1_to_b n (immF1 b).tape (b.h-1) hw1 hones1 hzero1)
  have hmiddle : run 1 (immB1 n b) = some (immF2 n b) := by
    dsimp [immB1] at hb1
    simp [run,next,immB1,immF2,hb1,show b.h-2-1=b.h-3 by omega]
  have h2 : run (4*m+5) (immF2 n b) = some (immB2 n m b) := by
    simpa [immF2,immB2,show b.h-3-1 = b.h-4 by omega] using
      (odd_f1_to_b m (immF2 n b).tape (b.h-3) hw2 hones2 hzero2)
  have htime : 4*n+4*m+20 = 9 + ((4*n+5) + (1+(4*m+5))) := by omega
  rw [htime,run_add,hp]
  simp only [Option.bind_some]
  rw [run_add,h1]
  simp only [Option.bind_some]
  rw [run_add,hmiddle]
  simp only [Option.bind_some]
  exact h2

/-- Both waves leave every cell at or left of the B/0 endpoint unchanged. -/
theorem imm_two_wave_left (n m : Nat) (b : Conf) (x : Int)
    (hx : x ≤ b.h-4) : (immB2 n m b).tape x = b.tape x := by
  calc
    (immB2 n m b).tape x = (immF2 n b).tape x := by
      exact oddWaveTape_left m (immF2 n b).tape (b.h-3) x (by omega)
    _ = (immB1 n b).tape x := by
      simp [immF2,setBit,show x ≠ b.h-2 by omega]
    _ = (immF1 b).tape x := by
      exact oddWaveTape_left n (immF1 b).tape (b.h-1) x (by omega)
    _ = b.tape x := by
      exact twoWavePrefixTape_left b.tape b.h x hx

/-- Return reads zero and transports the full forbidden-word shield. -/
theorem imm_two_wave_endpoint_shield (n m : Nat) (b : Conf)
    (hz : b.tape (b.h-4) = false)
    (hshield : NoLeft4 true true false b) :
    (immB2 n m b).q = .B ∧
    (immB2 n m b).tape (immB2 n m b).h = false ∧
    NoLeft4 true true false (immB2 n m b) := by
  refine ⟨rfl,?_,?_⟩
  · change (immB2 n m b).tape (b.h-4) = false
    exact (imm_two_wave_left n m b (b.h-4) (by omega)).trans hz
  · apply noLeft4_transfer_of_left_agreement true true false b (immB2 n m b)
      (by simp [immB2];omega)
    · intro x hx
      exact imm_two_wave_left n m b x (by simp [immB2] at hx; omega)
    · exact hshield

#print axioms BB6Root119.imm_two_wave_exact
#print axioms BB6Root119.imm_two_wave_left
#print axioms BB6Root119.imm_two_wave_endpoint_shield
end BB6Root119
