import Root119PrefixShield
import Root119CPhaseReturn

set_option linter.unusedSimpArgs false

namespace BB6Root119

/-- The five cells immediately before an even-sweep B/0 endpoint form 11101.
    The n=0 case is supplied by the two untouched prefix cells. -/
theorem evenSweepBResultTape_cphaseD1_pattern
    (n : Nat) (t : Int → Bool) (h : Int)
    (hprev0 : n = 0 → t (h-1) = false)
    (hprev1 : n = 0 → t (h-2) = true) :
    evenSweepBResultTape n t h (h+2*(n:Int)+2) = true ∧
    evenSweepBResultTape n t h (h+2*(n:Int)+1) = true ∧
    evenSweepBResultTape n t h (h+2*(n:Int)) = true ∧
    evenSweepBResultTape n t h (h+2*(n:Int)-1) = false ∧
    evenSweepBResultTape n t h (h+2*(n:Int)-2) = true := by
  let p : Int := h+2*(n+1)
  have hp : p = h+2*(n:Int)+2 := by dsimp [p]; omega
  have hkeep (x : Int) (hx0 : x ≠ p) (hx1 : x ≠ p-1) :
      evenSweepBResultTape n t h x = evenSweepTape (n+1) t h x := by
    simp [evenSweepBResultTape, p, setBit, hx0, hx1]
  have hhead : evenSweepBResultTape n t h (h+2*(n:Int)+2) = true := by
    rw [hp.symm]
    simp [evenSweepBResultTape, p, setBit]
  have hprev : evenSweepBResultTape n t h (h+2*(n:Int)+1) = true := by
    have hidx : h+2*(n:Int)+1 = p-1 := by rw [hp]; omega
    rw [hidx]
    simp [evenSweepBResultTape, p, setBit]
  have hmid : evenSweepBResultTape n t h (h+2*(n:Int)) = true := by
    have hidx : h+2*(n:Int) = p-2 := by rw [hp]; omega
    rw [hidx, hkeep (p-2) (by omega) (by omega), ← hidx]
    exact evenSweepTape_evenCell (n+1) t h n (by omega)
  have hminus1 : evenSweepBResultTape n t h (h+2*(n:Int)-1) = false := by
    cases n with
    | zero =>
        have hcoord0 : h+2*((0:Nat):Int)-1 = h-1 := by omega
        rw [hcoord0]
        have hidx : h-1 = p-3 := by dsimp [p]; omega
        rw [hidx, hkeep (p-3) (by omega) (by omega)]
        have hleft := evenSweepTape_left 1 t h (p-3) (by dsimp [p]; omega)
        rw [hleft]
        have hcoord : p-3 = h-1 := by dsimp [p]; omega
        rw [hcoord]
        exact hprev0 rfl
    | succ k =>
        change evenSweepBResultTape (k+1) t h (h+2*((k+1):Int)-1) = false
        have hidx : h+2*((k+1):Int)-1 = p-3 := by dsimp [p]; omega
        rw [hidx, hkeep (p-3) (by omega) (by omega)]
        have hcoord : p-3 = h+2*(k:Int)+1 := by dsimp [p]; omega
        rw [hcoord]
        exact evenSweepTape_oddCell (k+2) t h k (by omega)
  have hminus2 : evenSweepBResultTape n t h (h+2*(n:Int)-2) = true := by
    cases n with
    | zero =>
        have hcoord0 : h+2*((0:Nat):Int)-2 = h-2 := by omega
        rw [hcoord0]
        have hidx : h-2 = p-4 := by dsimp [p]; omega
        rw [hidx, hkeep (p-4) (by omega) (by omega)]
        have hleft := evenSweepTape_left 1 t h (p-4) (by dsimp [p]; omega)
        rw [hleft]
        have hcoord : p-4 = h-2 := by dsimp [p]; omega
        rw [hcoord]
        exact hprev1 rfl
    | succ k =>
        change evenSweepBResultTape (k+1) t h (h+2*((k+1):Int)-2) = true
        have hidx : h+2*((k+1):Int)-2 = p-4 := by dsimp [p]; omega
        rw [hidx, hkeep (p-4) (by omega) (by omega)]
        have hcoord : p-4 = h+2*(k:Int) := by dsimp [p]; omega
        rw [hcoord]
        exact evenSweepTape_evenCell (k+2) t h k (by omega)
  exact ⟨hhead,hprev,hmid,hminus1,hminus2⟩

/-- Every exact even-prefix return is immediately followed by the universal
    r=3 C-phase D1 return. The composition returns at h+2n+1, preserving the
    1100 shield and excluding the authentic BBad gate. -/
theorem b0_even_prefix_then_cphaseD1 (b : Conf) (n : Nat)
    (hb : Reach b) (hb0 : BZero b)
    (hleft : b.tape (b.h-1) = true)
    (hzero : b.tape (b.h-2) = false)
    (hone : b.tape (b.h-3) = true)
    (hones : ∀ j : Nat, j < 2*n+1 → b.tape (b.h+1+(j:Int)) = true)
    (hterminal : b.tape (b.h+(2*(n+1):Int)) = false)
    (hfinal : b.tape (b.h+(2*(n+1):Int)+1) = false)
    (hshield : NoLeft4 true true false b) :
    ∃ bout, run (2*n+25) b = some bout ∧ Reach bout ∧ BZero bout ∧
      NoLeft4 true true false bout ∧ bout.h = b.h+2*(n:Int)+1 ∧ ¬BBad bout := by
  obtain ⟨b1,hrun1,hreach1,hB1,hhead1,htape1⟩ :=
    b0_even_prefix_to_b0_exact b n hb hb0 hleft hzero hone hones hterminal hfinal
  obtain ⟨b1',hrun1',hreach1',hB1',hshield1'⟩ :=
    b0_even_prefix_to_b0_preserves_NoLeft4 b n hb hb0 hleft hzero hone
      hones hterminal hfinal hshield
  have heq : b1' = b1 := Option.some.inj (hrun1'.symm.trans hrun1)
  have hreach1b : Reach b1 := by simpa [heq] using hreach1'
  have hB1b : BZero b1 := by simpa [heq] using hB1'
  have hshield1b : NoLeft4 true true false b1 := by simpa [heq] using hshield1'
  let dTape : Int → Bool :=
    setBit (twoWavePrefixTape b.tape b.h) (b.h-1) false
  have hprev0 : n = 0 → dTape (b.h-1) = false := by
    intro _
    simp [dTape,setBit]
  have hprev1 : n = 0 → dTape (b.h-2) = true := by
    intro _
    simp [dTape,twoWavePrefixTape,setBit] <;> omega
  have hpat := evenSweepBResultTape_cphaseD1_pattern n dTape b.h hprev0 hprev1
  have htape1' : b1.tape = evenSweepBResultTape n dTape b.h := by
    simpa [dTape] using htape1
  have hscan : ∀ i : Nat, i < 3 → b1.tape (b1.h-1-(i:Int)) = true := by
    intro i hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hc with hi0 | hi1 | hi2
    · subst i
      have hidx : b1.h-1-((0:Nat):Int) = b.h+2*(n:Int)+2 := by rw [hhead1]; omega
      rw [htape1',hidx]
      exact hpat.1
    · subst i
      have hidx : b1.h-1-((1:Nat):Int) = b.h+2*(n:Int)+1 := by rw [hhead1]; omega
      rw [htape1',hidx]
      exact hpat.2.1
    · subst i
      have hidx : b1.h-1-((2:Nat):Int) = b.h+2*(n:Int) := by rw [hhead1]; omega
      rw [htape1',hidx]
      exact hpat.2.2.1
  have hzeroC : b1.tape (b1.h-1-(3:Int)) = false := by
    have hidx : b1.h-1-(3:Int) = b.h+2*(n:Int)-1 := by rw [hhead1]; omega
    rw [htape1',hidx]
    exact hpat.2.2.2.1
  have honeD : b1.tape (b1.h-2-(3:Int)) = true := by
    have hidx : b1.h-2-(3:Int) = b.h+2*(n:Int)-2 := by rw [hhead1]; omega
    rw [htape1',hidx]
    exact hpat.2.2.2.2
  obtain ⟨bout,htail,hreach2,hB2,hhead2,hshield2,hnotBad⟩ :=
    b0_cphase_d1_zero_wave_return b1 3 hreach1b hB1b (by omega)
      hscan hzeroC honeD hshield1b
  have hrun2 : run 10 b1 = some bout := by
    rw [run_eq_shuttleRun]
    exact htail
  have hrun2' : run 10 b1' = some bout := by simpa [heq] using hrun2
  have hrun : run (2*n+25) b = some bout := by
    have htime : 2*n+25 = (2*n+15)+10 := by omega
    rw [htime,run_add,hrun1']
    simp [hrun2']
  have hheadFinal : bout.h = b.h+2*(n:Int)+1 := by
    calc
      bout.h = b1.h-(3:Int)+1 := hhead2
      _ = b.h+2*(n:Int)+1 := by rw [hhead1]; omega
  exact ⟨bout,hrun,hreach2,hB2,hshield2,hheadFinal,hnotBad⟩

/-- The odd-even prefix has the same 11101 left boundary at its B/0 return.
    Under its necessary boundary guard, it therefore enters the same r=3
    C-phase D1 return and preserves the shield. -/
theorem b0_odd_even_prefix_then_cphaseD1 (b : Conf) (n : Nat)
    (hb : Reach b) (hb0 : BZero b)
    (hleft : b.tape (b.h-1) = true)
    (hzero : b.tape (b.h-2) = false)
    (hone : b.tape (b.h-3) = true)
    (hones : ∀ j : Nat, j < 2*n → b.tape (b.h+1+(j:Int)) = true)
    (hterminal1 : b.tape (b.h+(2*n+1:Int)) = false)
    (hterminal2 : b.tape (b.h+(2*n+2:Int)) = false)
    (hfinal : b.tape (b.h+(2*n+3:Int)) = false)
    (hshield : NoLeft4 true true false b)
    (hboundary : ¬(b.tape (b.h-6) = true ∧ b.tape (b.h-5) = true ∧
      b.tape (b.h-4) = false)) :
    ∃ bout, run (6*n+33) b = some bout ∧ Reach bout ∧ BZero bout ∧
      NoLeft4 true true false bout ∧ bout.h = b.h+2*(n:Int)+1 ∧ ¬BBad bout := by
  obtain ⟨b1,hrun1,hreach1,hB1,hhead1,htape1⟩ :=
    b0_odd_even_chain_to_b0_exact b n hb hb0 hleft hzero hone hones
      hterminal1 hterminal2 hfinal
  obtain ⟨b1',hrun1',hreach1',hB1',hshield1'⟩ :=
    b0_odd_even_chain_to_b0_preserves_NoLeft4 b n hb hb0 hleft hzero hone
      hones hterminal1 hterminal2 hfinal hshield hboundary
  have heq : b1' = b1 := Option.some.inj (hrun1'.symm.trans hrun1)
  have hreach1b : Reach b1 := by simpa [heq] using hreach1'
  have hB1b : BZero b1 := by simpa [heq] using hB1'
  have hshield1b : NoLeft4 true true false b1 := by simpa [heq] using hshield1'
  let dTape : Int → Bool :=
    setBit (setBit (oddWaveTape n (twoWavePrefixTape b.tape b.h) (b.h-1))
      (b.h-2) true) (b.h-3) false
  have hpat := evenSweepBResultTape_cphaseD1_pattern (n+1) dTape (b.h-2)
    (by intro hn; omega) (by intro hn; omega)
  have hpat0 : b.h+2*(n:Int)+2 = (b.h-2)+2*((n+1):Int)+2 := by omega
  have hpat1 : b.h+2*(n:Int)+1 = (b.h-2)+2*((n+1):Int)+1 := by omega
  have hpat2 : b.h+2*(n:Int) = (b.h-2)+2*((n+1):Int) := by omega
  have hpat3 : b.h+2*(n:Int)-1 = (b.h-2)+2*((n+1):Int)-1 := by omega
  have hpat4 : b.h+2*(n:Int)-2 = (b.h-2)+2*((n+1):Int)-2 := by omega
  have htape1' : b1.tape = evenSweepBResultTape (n+1) dTape (b.h-2) := by
    simpa [dTape] using htape1
  have hscan : ∀ i : Nat, i < 3 → b1.tape (b1.h-1-(i:Int)) = true := by
    intro i hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hc with hi0 | hi1 | hi2
    · subst i
      have hidx : b1.h-1-((0:Nat):Int) = b.h+2*(n:Int)+2 := by rw [hhead1]; omega
      rw [htape1',hidx,hpat0]
      exact hpat.1
    · subst i
      have hidx : b1.h-1-((1:Nat):Int) = b.h+2*(n:Int)+1 := by rw [hhead1]; omega
      rw [htape1',hidx,hpat1]
      exact hpat.2.1
    · subst i
      have hidx : b1.h-1-((2:Nat):Int) = b.h+2*(n:Int) := by rw [hhead1]; omega
      rw [htape1',hidx,hpat2]
      exact hpat.2.2.1
  have hzeroC : b1.tape (b1.h-1-(3:Int)) = false := by
    have hidx : b1.h-1-(3:Int) = b.h+2*(n:Int)-1 := by rw [hhead1]; omega
    rw [htape1',hidx,hpat3]
    exact hpat.2.2.2.1
  have honeD : b1.tape (b1.h-2-(3:Int)) = true := by
    have hidx : b1.h-2-(3:Int) = b.h+2*(n:Int)-2 := by rw [hhead1]; omega
    rw [htape1',hidx,hpat4]
    exact hpat.2.2.2.2
  obtain ⟨bout,htail,hreach2,hB2,hhead2,hshield2,hnotBad⟩ :=
    b0_cphase_d1_zero_wave_return b1 3 hreach1b hB1b (by omega)
      hscan hzeroC honeD hshield1b
  have hrun2 : run 10 b1 = some bout := by
    rw [run_eq_shuttleRun]
    exact htail
  have hrun2' : run 10 b1' = some bout := by simpa [heq] using hrun2
  have hrun : run (6*n+33) b = some bout := by
    have htime : 6*n+33 = (6*n+23)+10 := by omega
    rw [htime,run_add,hrun1']
    simp [hrun2']
  have hheadFinal : bout.h = b.h+2*(n:Int)+1 := by
    calc
      bout.h = b1.h-(3:Int)+1 := hhead2
      _ = b.h+2*(n:Int)+1 := by rw [hhead1]; omega
  exact ⟨bout,hrun,hreach2,hB2,hshield2,hheadFinal,hnotBad⟩

#print axioms BB6Root119.evenSweepBResultTape_cphaseD1_pattern
#print axioms BB6Root119.b0_even_prefix_then_cphaseD1
#print axioms BB6Root119.b0_odd_even_prefix_then_cphaseD1
end BB6Root119
