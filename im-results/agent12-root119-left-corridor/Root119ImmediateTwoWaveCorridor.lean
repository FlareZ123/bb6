import Root119ImmediateTwoWave
namespace BB6Root119

theorem imm_setBit_away (t : Int → Bool) (h x : Int) (v : Bool)
    (hx : x ≠ h) : setBit t h v x = t x := by
  simp [setBit,hx]

/-- Physical 1^(2n)010 input corridor produces two immediate odd waves. -/
theorem imm_two_wave_concrete (n : Nat) (b : Conf)
    (hb : BZero b)
    (hl1 : b.tape (b.h-1) = true)
    (hl2 : b.tape (b.h-2) = false)
    (hl3 : b.tape (b.h-3) = true)
    (hl4 : b.tape (b.h-4) = false)
    (hones : ∀ j : Nat, j < 2*n → b.tape (b.h+1+(j:Int)) = true)
    (hz1 : b.tape (b.h+2*(n:Int)+1) = false)
    (ho2 : b.tape (b.h+2*(n:Int)+2) = true)
    (hz2 : b.tape (b.h+2*(n:Int)+3) = false)
    (hshield : NoLeft4 true true false b) :
    run (8*n+28) b = some (immB2 n (n+2) b) ∧
    BZero (immB2 n (n+2) b) ∧
    NoLeft4 true true false (immB2 n (n+2) b) := by
  have hfHead : (immF1 b).tape (b.h-1) = true := by
    simp (disch := omega) [immF1,twoWavePrefixTape,setBit]
  have hfOnes : ∀ j : Nat, j < 2*n+1 →
      (immF1 b).tape (b.h-1+1+(j:Int)) = true := by
    intro j hj
    cases j with
    | zero => simp (disch := omega) [immF1,twoWavePrefixTape,setBit]
    | succ k =>
      have hk : k < 2*n := by omega
      have heq : b.h-1+1+((k+1:Nat):Int) = b.h+1+(k:Int) := by omega
      change (twoWavePrefixTape b.tape b.h) (b.h-1+1+((k+1:Nat):Int)) = true
      rw [heq,twoWavePrefixTape_right b.tape b.h _ (by omega)]
      exact hones k hk
  have hfZero : (immF1 b).tape (b.h-1+2*(n:Int)+2) = false := by
    change (twoWavePrefixTape b.tape b.h) (b.h-1+2*(n:Int)+2) = false
    have heq : b.h-1+2*(n:Int)+2=b.h+2*(n:Int)+1 := by omega
    rw [heq,twoWavePrefixTape_right b.tape b.h _ (by omega)]
    exact hz1
  have hb1 : (immB1 n b).tape (b.h-2) = true := by
    change oddWaveTape n (immF1 b).tape (b.h-1) (b.h-2) = true
    rw [oddWaveTape_left n (immF1 b).tape (b.h-1) (b.h-2) (by omega)]
    simp (disch := omega) [immF1,twoWavePrefixTape,setBit]
  have hf2Head : (immF2 n b).tape (b.h-3) = true := by
    change setBit (immB1 n b).tape (b.h-2) true (b.h-3) = true
    rw [imm_setBit_away (immB1 n b).tape (b.h-2) (b.h-3) true (by omega)]
    change oddWaveTape n (immF1 b).tape (b.h-1) (b.h-3) = true
    rw [oddWaveTape_left n (immF1 b).tape (b.h-1) (b.h-3) (by omega)]
    simp (disch := omega) [immF1,twoWavePrefixTape,setBit]
  have hf2Ones : ∀ j : Nat, j < 2*(n+2)+1 →
      (immF2 n b).tape (b.h-3+1+(j:Int)) = true := by
    intro j hj
    by_cases hj0 : j=0
    · subst j
      simp (disch := omega) [immF2,setBit]
      omega
    have hj1 : j ≥ 1 := by omega
    have hposNe : b.h-3+1+(j:Int) ≠ b.h-2 := by omega
    have hposEq : b.h-3+1+(j:Int) = b.h-2+(j:Int) := by omega
    change (setBit (immB1 n b).tape (b.h-2) true) (b.h-3+1+(j:Int)) = true
    rw [imm_setBit_away (immB1 n b).tape (b.h-2) _ true hposNe]
    change oddWaveTape n (immF1 b).tape (b.h-1) (b.h-3+1+(j:Int)) = true
    by_cases hj1eq : j=1
    · have heq : b.h-3+1+(j:Int)=b.h-1 := by omega
      rw [heq]
      exact oddWaveTape_head n (immF1 b).tape (b.h-1)
    by_cases hjlast : j=2*n+4
    · have heq : b.h-3+1+(j:Int)=b.h+2*(n:Int)+2 := by omega
      rw [heq,oddWaveTape_outside_right n (immF1 b).tape (b.h-1) _ (by omega)]
      change (twoWavePrefixTape b.tape b.h) (b.h+2*(n:Int)+2) = true
      rw [twoWavePrefixTape_right b.tape b.h _ (by omega)]
      exact ho2
    · have hjRange : 2 ≤ j ∧ j < 2*n+4 := by omega
      have hk : j-2 < 2*n+2 := by omega
      have heq : b.h-3+1+(j:Int)=b.h-1+1+((j-2:Nat):Int) := by omega
      rw [heq]
      exact oddWaveTape_filled n (immF1 b).tape (b.h-1) (j-2) hk
  have hf2Zero : (immF2 n b).tape (b.h-3+2*((n+2:Int))+2) = false := by
    have heq : b.h-3+2*((n+2:Int))+2 = b.h+2*(n:Int)+3 := by omega
    change (setBit (immB1 n b).tape (b.h-2) true) (b.h-3+2*((n+2:Int))+2) = false
    rw [heq,imm_setBit_away (immB1 n b).tape (b.h-2) _ true (by omega)]
    change oddWaveTape n (immF1 b).tape (b.h-1) (b.h+2*(n:Int)+3) = false
    rw [oddWaveTape_outside_right n (immF1 b).tape (b.h-1) _ (by omega)]
    change (twoWavePrefixTape b.tape b.h) (b.h+2*(n:Int)+3) = false
    rw [twoWavePrefixTape_right b.tape b.h _ (by omega)]
    exact hz2
  have hRun := imm_two_wave_exact n (n+2) b hb hl1 hl2 hl3
    hfHead hfOnes hfZero hb1 hf2Head hf2Ones hf2Zero
  have hEnd := imm_two_wave_endpoint_shield n (n+2) b hl4 hshield
  have hTime : 8*n+28=4*n+4*(n+2)+20 := by omega
  rw [hTime]
  exact ⟨hRun,⟨hEnd.1,hEnd.2.1⟩,hEnd.2.2⟩

#print axioms BB6Root119.imm_two_wave_concrete
end BB6Root119
