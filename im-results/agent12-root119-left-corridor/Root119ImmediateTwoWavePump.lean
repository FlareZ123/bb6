import Root119ImmediateTwoWaveCorridor

namespace BB6Root119

/-- A finite alternating left corridor, read nearest cell first: 1,0,1,0,... . -/
def leftAlternating (k : Nat) (b : Conf) : Prop :=
  ∀ j : Nat, j < 4*k+4 →
    b.tape (b.h-1-(j:Int)) = decide (j % 2 = 0)

/-- A finite alternating right sentinel after a 1-run, read from the first
    cell after the run: 0,1,0,1,... . -/
def rightAlternating (k n : Nat) (b : Conf) : Prop :=
  ∀ j : Nat, j < 4*k+4 →
    b.tape (b.h+2*(n:Int)+1+(j:Int)) = decide (j % 2 = 1)

/-- One exact two-wave return consumes four alternating cells on each side
    of the run, moves the B/0 head four cells left, and grows the right run
    by eight.  The untouched remaining alternating corridors are retained,
    so the step can be iterated. -/
theorem imm_two_wave_pump_step (k n : Nat) (b : Conf)
    (hb : BZero b) (hr : Reach b)
    (hshield : NoLeft4 true true false b)
    (hleft : leftAlternating (k+1) b)
    (hones : ∀ j : Nat, j < 2*n →
      b.tape (b.h+1+(j:Int)) = true)
    (hright : rightAlternating (k+1) n b) :
    ∃ bout : Conf,
      run (8*n+28) b = some bout ∧
      Reach bout ∧ BZero bout ∧
      NoLeft4 true true false bout ∧
      bout.h = b.h-4 ∧
      leftAlternating k bout ∧
      (∀ j : Nat, j < 2*n+8 →
        bout.tape (bout.h+1+(j:Int)) = true) ∧
      rightAlternating k (n+4) bout := by
  have hl1 : b.tape (b.h-1) = true := by
    have h := hleft 0 (by omega)
    simpa using h
  have hl2 : b.tape (b.h-2) = false := by
    have h := hleft 1 (by omega)
    simpa using h
  have hl3 : b.tape (b.h-3) = true := by
    have h := hleft 2 (by omega)
    simpa using h
  have hl4 : b.tape (b.h-4) = false := by
    have h := hleft 3 (by omega)
    simpa using h
  have hl5 : b.tape (b.h-5) = true := by
    have h := hleft 4 (by omega)
    simpa using h
  have hl6 : b.tape (b.h-6) = false := by
    have h := hleft 5 (by omega)
    simpa using h
  have hl7 : b.tape (b.h-7) = true := by
    have h := hleft 6 (by omega)
    simpa using h
  have hl8 : b.tape (b.h-8) = false := by
    have h := hleft 7 (by omega)
    simpa using h
  have hz1 : b.tape (b.h+2*(n:Int)+1) = false := by
    have h := hright 0 (by omega)
    simpa using h
  have ho2 : b.tape (b.h+2*(n:Int)+2) = true := by
    have h := hright 1 (by omega)
    simpa using h
  have hz2 : b.tape (b.h+2*(n:Int)+3) = false := by
    have h := hright 2 (by omega)
    simpa using h
  have ho3 : b.tape (b.h+2*(n:Int)+4) = true := by
    have h := hright 3 (by omega)
    simpa using h
  have hz3 : b.tape (b.h+2*(n:Int)+5) = false := by
    have h := hright 4 (by omega)
    simpa using h
  have ho4 : b.tape (b.h+2*(n:Int)+6) = true := by
    have h := hright 5 (by omega)
    simpa using h
  have hz4 : b.tape (b.h+2*(n:Int)+7) = false := by
    have h := hright 6 (by omega)
    simpa using h
  have ho5 : b.tape (b.h+2*(n:Int)+8) = true := by
    have h := hright 7 (by omega)
    simpa using h

  let bout : Conf := immB2 n (n+2) b
  have hmacro := imm_two_wave_concrete n b hb hl1 hl2 hl3 hl4
    hones hz1 ho2 hz2 hshield
  have hrun : run (8*n+28) b = some bout := by
    simpa [bout] using hmacro.1
  have hB : BZero bout := by
    simpa [bout] using hmacro.2.1
  have hNoLeft : NoLeft4 true true false bout := by
    simpa [bout] using hmacro.2.2
  have hhead : bout.h = b.h-4 := by
    rfl
  have hreach : Reach bout :=
    reachable_of_run (8*n+28) b bout hr hrun

  have hleftTape (x : Int) (hx : x ≤ b.h-4) :
      bout.tape x = b.tape x := by
    simpa [bout] using imm_two_wave_left n (n+2) b x hx

  have htail (x : Int) (hx : b.h+2*(n:Int)+4 ≤ x) :
      bout.tape x = b.tape x := by
    change oddWaveTape (n+2) (immF2 n b).tape (b.h-3) x = b.tape x
    have h2 := oddWaveTape_outside_right (n+2) (immF2 n b).tape
      (b.h-3) x (by omega)
    rw [h2]
    change (immF2 n b).tape x = b.tape x
    dsimp [immF2]
    have hne : x ≠ b.h-2 := by omega
    rw [setBit_apply_ne _ _ _ _ hne]
    change oddWaveTape n (immF1 b).tape (b.h-1) x = b.tape x
    have h1 := oddWaveTape_outside_right n (immF1 b).tape
      (b.h-1) x (by omega)
    rw [h1]
    change twoWavePrefixTape b.tape b.h x = b.tape x
    exact twoWavePrefixTape_right b.tape b.h x (by omega)

  have hrunRight : ∀ j : Nat, j < 2*n+8 →
      bout.tape (bout.h+1+(j:Int)) = true := by
    intro j hj
    have hcoord : bout.h+1+(j:Int) = b.h-3+(j:Int) := by
      rw [hhead]
      omega
    rw [hcoord]
    by_cases hj0 : j = 0
    · subst j
      change oddWaveTape (n+2) (immF2 n b).tape (b.h-3) (b.h-3) = true
      exact oddWaveTape_head (n+2) (immF2 n b).tape (b.h-3)
    · by_cases hjlast : j = 2*n+7
      · subst j
        have hkeep := htail (b.h+2*(n:Int)+4) (by omega)
        have hidx : b.h-3+((2*n+7:Nat):Int) =
            b.h+2*(n:Int)+4 := by omega
        rw [hidx]
        exact hkeep.trans ho3
      · have hjpos : 1 ≤ j := by omega
        have hk : j-1 < 2*(n+2)+2 := by omega
        have hidx : b.h-3+(j:Int) =
            b.h-3+1+((j-1:Int)) := by omega
        rw [hidx]
        change oddWaveTape (n+2) (immF2 n b).tape
          (b.h-3) (b.h-3+1+((j-1:Int))) = true
        exact oddWaveTape_filled (n+2) (immF2 n b).tape
          (b.h-3) (j-1) hk

  have hleftOut : leftAlternating k bout := by
    intro j hj
    have hidx : bout.h-1-(j:Int) =
        b.h-1-((j+4):Int) := by
      rw [hhead]
      omega
    rw [hidx]
    have hkeep := hleftTape (b.h-1-((j+4):Int)) (by omega)
    rw [hkeep]
    have hj' : j+4 < 4*(k+1)+4 := by omega
    have hv := hleft (j+4) hj'
    have hmod : (j+4)%2 = j%2 := by omega
    simpa [hmod] using hv

  have hrightOut : rightAlternating k (n+4) bout := by
    intro j hj
    have hidx : bout.h+2*((n+4):Int)+1+(j:Int) =
        b.h+2*(n:Int)+5+(j:Int) := by
      rw [hhead]
      omega
    rw [hidx]
    have hkeep := htail (b.h+2*(n:Int)+5+(j:Int)) (by omega)
    rw [hkeep]
    have hcoord : b.h+2*(n:Int)+5+(j:Int) =
        b.h+2*(n:Int)+1+((j+4):Int) := by omega
    rw [hcoord]
    have hj' : j+4 < 4*(k+1)+4 := by omega
    have hv := hright (j+4) hj'
    have hmod : (j+4)%2 = j%2 := by omega
    simpa [hmod] using hv

  exact ⟨bout,hrun,hreach,hB,hNoLeft,hhead,hleftOut,hrunRight,hrightOut⟩

/-- Total transition cost for k iterations of the two-wave pump. -/
def twoWavePumpCost (k n : Nat) : Nat :=
  8*n*k + 16*k*(k-1) + 28*k

/-- Iterating the exact two-wave pump k times gives a reached B/0 whose
    right one-run has grown by 8k, whose head has moved left by 4k, and
    whose alternating left and right boundary corridors remain available.
    The proof is an induction over the source-machine run, not a simulation. -/
theorem imm_two_wave_pump_iter (k n : Nat) (b : Conf)
    (hb : BZero b) (hr : Reach b)
    (hshield : NoLeft4 true true false b)
    (hleft : leftAlternating k b)
    (hones : ∀ j : Nat, j < 2*n →
      b.tape (b.h+1+(j:Int)) = true)
    (hright : rightAlternating k n b) :
    ∃ bout : Conf,
      run (twoWavePumpCost k n) b = some bout ∧
      Reach bout ∧ BZero bout ∧
      NoLeft4 true true false bout ∧
      bout.h = b.h-4*(k:Int) ∧
      (∀ j : Nat, j < 2*n+8*k →
        bout.tape (bout.h+1+(j:Int)) = true) ∧
      leftAlternating 0 bout ∧
      rightAlternating 0 (n+4*k) bout := by
  revert n b hb hr hshield hleft hones hright
  induction k with
  | zero =>
      intro n b hb hr hshield hleft hones hright
      refine ⟨b,?_,hr,hb,hshield,?_,?_,hleft,?⟩
      · simp [twoWavePumpCost]
      · simp
      · simpa using hones
      · simpa using hright
  | succ k ih =>
      intro n b hb hr hshield hleft hones hright
      obtain ⟨b1,hstepRun,hreach1,hB1,hshield1,hhead1,hleft1,hones1,hright1⟩ :=
        imm_two_wave_pump_step k n b hb hr hshield hleft hones hright
      obtain ⟨bout,hiterRun,hreach,hB,hshieldOut,hheadOut,
          honesOut,hleftOut,hrightOut⟩ :=
        ih (n+4) b1 hB1 hreach1 hshield1 hleft1 hones1 hright1
      have hcost : twoWavePumpCost (k+1) n =
          (8*n+28)+twoWavePumpCost k (n+4) := by
        simp [twoWavePumpCost]
        omega
      have hrun : run (twoWavePumpCost (k+1) n) b = some bout := by
        have hcomp := run_add (8*n+28) (twoWavePumpCost k (n+4)) b
        rw [hcost,hcomp,hstepRun]
        simp [hiterRun]
      have hhead : bout.h = b.h-4*((k+1):Int) := by
        calc
          bout.h = b1.h-4*(k:Int) := hheadOut
          _ = b.h-4-4*(k:Int) := by rw [hhead1]
          _ = b.h-4*((k+1):Int) := by omega
      have honesFinal : ∀ j : Nat, j < 2*n+8*(k+1) →
          bout.tape (bout.h+1+(j:Int)) = true := by
        intro j hj
        apply honesOut
        omega
      have hrightFinal : rightAlternating 0 (n+4*(k+1)) bout := by
        have hpar : (n+4)+4*k = n+4*(k+1) := by omega
        simpa [hpar] using hrightOut
      exact ⟨bout,hrun,hreach,hB,hshieldOut,hhead,honesFinal,
        hleftOut,hrightFinal⟩

#print axioms BB6Root119.imm_two_wave_pump_step
#print axioms BB6Root119.imm_two_wave_pump_iter

end BB6Root119
