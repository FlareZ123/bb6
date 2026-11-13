import Root119ZeroLeftShield
import Root119CPhaseReturn
set_option linter.unusedSimpArgs false
namespace BB6Root119

/-- Any finite shuttleRun from a reached configuration ends at a reached configuration. -/
theorem evenSweepTape_evenCell (n : Nat) (t : Int → Bool) (h : Int)
    (j : Nat) (hj : j < n) :
    evenSweepTape n t h (h+2*(j:Int)) = true := by
  induction n generalizing t h j with
  | zero => omega
  | succ n ih =>
      by_cases hj0 : j = 0
      · subst j
        simp only [evenSweepTape]
        have hidx : h+2*((0:Nat):Int) = h := by omega
        rw [hidx]
        have hleft := evenSweepTape_left n
          (setBit (setBit t h true) (h+1) false) (h+2) h (by omega)
        rw [hleft]
        simp [setBit, show h ≠ h+1 by omega]
      · have hj' : j-1 < n := by omega
        have hidx : h+2*(j:Int) = (h+2)+2*((j-1:Nat):Int) := by omega
        simp only [evenSweepTape]
        rw [hidx]
        exact ih (setBit (setBit t h true) (h+1) false) (h+2) (j-1) hj'

theorem evenSweepTape_oddCell (n : Nat) (t : Int → Bool) (h : Int)
    (j : Nat) (hj : j < n) :
    evenSweepTape n t h (h+2*(j:Int)+1) = false := by
  induction n generalizing t h j with
  | zero => omega
  | succ n ih =>
      by_cases hj0 : j = 0
      · subst j
        simp only [evenSweepTape]
        have hidx : h+2*((0:Nat):Int)+1 = h+1 := by omega
        rw [hidx]
        have hleft := evenSweepTape_left n
          (setBit (setBit t h true) (h+1) false) (h+2) (h+1) (by omega)
        rw [hleft]
        simp [setBit, show h+1 ≠ h by omega]
      · have hj' : j-1 < n := by omega
        have hidx : h+2*(j:Int)+1 = (h+2)+2*((j-1:Nat):Int)+1 := by omega
        simp only [evenSweepTape]
        rw [hidx]
        exact ih (setBit (setBit t h true) (h+1) false) (h+2) (j-1) hj'

theorem zeroLeftEvenOutTape_cphaseD1_pattern (n : Nat) (t : Int → Bool) (h : Int) :
    zeroLeftEvenOutTape n t h (h+2*(n:Int)+1) = true ∧
    zeroLeftEvenOutTape n t h (h+2*(n:Int)) = true ∧
    zeroLeftEvenOutTape n t h (h+2*(n:Int)-1) = true ∧
    zeroLeftEvenOutTape n t h (h+2*(n:Int)-2) = false ∧
    zeroLeftEvenOutTape n t h (h+2*(n:Int)-3) = true := by
  have hterm0 : h+2*(n:Int) = (h+1)+2*(n:Int)-1 := by omega
  have hterm1 : h+2*(n:Int)+1 = (h+1)+2*(n:Int) := by omega
  have hlast0 : zeroLeftEvenOutTape n t h (h+2*(n:Int)) = true := by
    change setBit (setBit (evenSweepTape n
      (setBit (zeroLeftPrefixTape t h) h false) (h+1))
      ((h+1)+2*(n:Int)-1) true) ((h+1)+2*(n:Int)) true
      (h+2*(n:Int)) = true
    rw [hterm0]
    simp [setBit]
  have hlast1 : zeroLeftEvenOutTape n t h (h+2*(n:Int)+1) = true := by
    change setBit (setBit (evenSweepTape n
      (setBit (zeroLeftPrefixTape t h) h false) (h+1))
      ((h+1)+2*(n:Int)-1) true) ((h+1)+2*(n:Int)) true
      (h+2*(n:Int)+1) = true
    rw [hterm1]
    simp [setBit]
  have hminus1 : zeroLeftEvenOutTape n t h (h+2*(n:Int)-1) = true := by
    cases n with
    | zero =>
        have hidx : h+2*((0:Nat):Int)-1 = h-1 := by omega
        rw [hidx]
        exact zeroLeftEvenOutTape_hm1 0 t h
    | succ k =>
        let fTape := setBit (zeroLeftPrefixTape t h) h false
        have hs := evenSweepTape_evenCell (k+1) fTape (h+1) k (by omega)
        have hidx : h+2*((k+1):Nat)-1 = (h+1)+2*(k:Int) := by omega
        have hne1 : (h+1)+2*(k:Int) ≠ (h+1)+2*((k+1):Int)-1 := by omega
        have hne2 : (h+1)+2*(k:Int) ≠ (h+1)+2*((k+1):Int) := by omega
        change setBit (setBit (evenSweepTape (k+1) fTape (h+1))
          ((h+1)+2*((k+1):Int)-1) true) ((h+1)+2*((k+1):Int)) true
          (h+2*((k+1):Nat)-1) = true
        rw [hidx]
        simp [setBit, hne1, hne2, hs]
  have hminus2 : zeroLeftEvenOutTape n t h (h+2*(n:Int)-2) = false := by
    cases n with
    | zero =>
        simpa using zeroLeftEvenOutTape_hm2 0 t h
    | succ k =>
      cases k with
      | zero =>
        simpa using zeroLeftEvenOutTape_h_false 1 t h (by omega)
      | succ k =>
        let fTape := setBit (zeroLeftPrefixTape t h) h false
        have hs := evenSweepTape_oddCell (k+2) fTape (h+1) k (by omega)
        have hidx : h+2*((k+2):Nat)-2 = (h+1)+2*(k:Int)+1 := by omega
        have hne1 : (h+1)+2*(k:Int)+1 ≠ (h+1)+2*((k+2):Int)-1 := by omega
        have hne2 : (h+1)+2*(k:Int)+1 ≠ (h+1)+2*((k+2):Int) := by omega
        change setBit (setBit (evenSweepTape (k+2) fTape (h+1))
          ((h+1)+2*((k+2):Int)-1) true) ((h+1)+2*((k+2):Int)) true
          (h+2*((k+2):Nat)-2) = false
        rw [hidx]
        simp [setBit, hne1, hne2, hs]
  have hminus3 : zeroLeftEvenOutTape n t h (h+2*(n:Int)-3) = true := by
    cases n with
    | zero =>
        have hidx : h+2*((0:Nat):Int)-3 = h-3 := by omega
        simpa [hidx] using zeroLeftEvenOutTape_hm3 0 t h
    | succ k =>
      cases k with
      | zero =>
        have hidx : h+2*((0+1:Nat):Int)-3 = h-1 := by omega
        rw [hidx]
        exact zeroLeftEvenOutTape_hm1 1 t h
      | succ k =>
        let fTape := setBit (zeroLeftPrefixTape t h) h false
        have hs := evenSweepTape_evenCell (k+2) fTape (h+1) k (by omega)
        have hidx : h+2*((k+2):Nat)-3 = (h+1)+2*(k:Int) := by omega
        have hne1 : (h+1)+2*(k:Int) ≠ (h+1)+2*((k+2):Int)-1 := by omega
        have hne2 : (h+1)+2*(k:Int) ≠ (h+1)+2*((k+2):Int) := by omega
        change setBit (setBit (evenSweepTape (k+2) fTape (h+1))
          ((h+1)+2*((k+2):Int)-1) true) ((h+1)+2*((k+2):Int)) true
          (h+2*((k+2):Nat)-3) = true
        rw [hidx]
        simp [setBit, hne1, hne2, hs]
  exact ⟨hlast1,hlast0,hminus1,hminus2,hminus3⟩

/-- Any finite shuttleRun from a reached configuration ends at a reached configuration. -/
theorem shuttleRun_reachable (n : Nat) (b d : Conf)
    (hb : Reach b) (hr : shuttleRun n b = some d) : Reach d := by
  induction n generalizing b d with
  | zero =>
      simp [shuttleRun] at hr
      cases hr
      exact hb
  | succ n ih =>
      cases hstep : next b with
      | none =>
          simp [shuttleRun,hstep] at hr
      | some c =>
          have hrest : shuttleRun n c = some d := by
            simpa [shuttleRun,hstep] using hr
          exact ih c d (Reach.follow hb hstep) hrest

/-- A zero-left even-run return is followed uniformly by the r=3 C-phase
    D1 wave: the composition returns to B/0 two cells to the right of the
    original head, preserving the 1100 shield and excluding BBad. -/
theorem zeroLeftEvenRun_then_cphaseD1
    (n : Nat) (b : Conf) (hb : Reach b)
    (hq : b.q = .B) (h0 : b.tape b.h = false)
    (h1 : b.tape (b.h-1) = false)
    (h2 : b.tape (b.h-2) = false)
    (h3 : b.tape (b.h-3) = false)
    (hones : ∀ j : Nat, j < 2*n →
      b.tape (b.h+1+(j:Int)) = true)
    (hzero : b.tape (b.h+2*(n:Int)+1) = false)
    (hzeroNext : b.tape (b.h+2*(n:Int)+2) = false)
    (hshield : NoLeft4 true true false b) :
    ∃ bout, shuttleRun (2*n+22) b = some bout ∧ Reach bout ∧
      BZero bout ∧ bout.h = b.h+2*(n:Int) ∧
      NoLeft4 true true false bout ∧ ¬BBad bout := by
  have hshieldTape : NoLeft1100 b.tape b.h := by
    intro x hx hw
    exact hshield x hx hw
  let d : Conf := ⟨.B,b.h+2*(n:Int)+2,
    zeroLeftEvenOutTape n b.tape b.h⟩
  have hfirst := zeroLeftEvenRun_exact_with_NoLeft1100 n b hq
    h0 h1 h2 h3 hones hzero hzeroNext hshieldTape
  have hrunFirst : shuttleRun (2*n+12) b = some d := by
    simpa [d] using hfirst.1
  have hdReach : Reach d :=
    shuttleRun_reachable (2*n+12) b d hb hrunFirst
  have hdB : BZero d := by
    constructor
    · rfl
    · change zeroLeftEvenOutTape n b.tape b.h
        (b.h+2*(n:Int)+2) = false
      exact zeroLeftEvenOutTape_head n b.tape b.h hzeroNext
  have hdShieldTape : NoLeft1100 d.tape d.h := by
    simpa [d] using hfirst.2
  have hdShield : NoLeft4 true true false d := by
    intro x hx hw
    exact hdShieldTape x hx hw
  have hpat := zeroLeftEvenOutTape_cphaseD1_pattern n b.tape b.h
  have hscan : ∀ i : Nat, i < 3 →
      d.tape (d.h-1-(i:Int)) = true := by
    intro i hi
    have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hcase with hi0 | hi1 | hi2
    · subst i
      have hidx : d.h-1-((0:Nat):Int) = b.h+2*(n:Int)+1 := by
        dsimp [d]; omega
      rw [hidx]
      exact hpat.1
    · subst i
      have hidx : d.h-1-((1:Nat):Int) = b.h+2*(n:Int) := by
        dsimp [d]; omega
      rw [hidx]
      exact hpat.2.1
    · subst i
      have hidx : d.h-1-((2:Nat):Int) = b.h+2*(n:Int)-1 := by
        dsimp [d]; omega
      rw [hidx]
      exact hpat.2.2.1
  have hzeroC : d.tape (d.h-1-(3:Int)) = false := by
    have hidx : d.h-1-(3:Int) = b.h+2*(n:Int)-2 := by
      dsimp [d]; omega
    rw [hidx]
    exact hpat.2.2.2.1
  have honeD : d.tape (d.h-2-(3:Int)) = true := by
    have hidx : d.h-2-(3:Int) = b.h+2*(n:Int)-3 := by
      dsimp [d]; omega
    rw [hidx]
    exact hpat.2.2.2.2
  obtain ⟨bout,htail,hreach,hB,hhead,hshieldOut,hnotBad⟩ :=
    b0_cphase_d1_zero_wave_return d 3 hdReach hdB (by omega)
      hscan hzeroC honeD hdShield
  have htime : 2*n+22 = (2*n+12)+10 := by omega
  have hrun : shuttleRun (2*n+22) b = some bout := by
    rw [htime,shuttleRun_add,hrunFirst]
    simpa using htail
  have hheadFinal : bout.h = b.h+2*(n:Int) := by
    calc
      bout.h = d.h-(3:Int)+1 := hhead
      _ = b.h+2*(n:Int) := by dsimp [d]; omega
  exact ⟨bout,hrun,hreach,hB,hheadFinal,hshieldOut,hnotBad⟩

#print axioms BB6Root119.shuttleRun_reachable
#print axioms BB6Root119.zeroLeftEvenRun_then_cphaseD1
end BB6Root119
