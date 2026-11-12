import Root119CPhaseReturn
import Root119CGate

namespace BB6Root119

/-- A B/0 state whose left tape is a finite 111(01)^m 0011 ladder.
    Each 10-step C/D/F/A/B retreat shortens the ladder by one pair. -/
structure MarkerB0Pattern (m : Nat) (b : Conf) : Prop where
  hB : BZero b
  left1 : b.tape (b.h-1) = true
  left2 : b.tape (b.h-2) = true
  left3 : b.tape (b.h-3) = true
  alternating : ∀ i : Nat, i < m →
    b.tape (b.h-4-2*(i:Int)) = false ∧
    b.tape (b.h-5-2*(i:Int)) = true
  final0 : b.tape (b.h-4-2*(m:Int)) = false
  final00 : b.tape (b.h-5-2*(m:Int)) = false
  final1 : b.tape (b.h-6-2*(m:Int)) = true
  final11 : b.tape (b.h-7-2*(m:Int)) = true

/-- The raw six-step C/0-D/1-F/1-D/0-E/0-A/0 tail.
    This is the same deterministic tail as the shielded C-phase lemma,
    but it does not assume NoLeft4: the forbidden marker may be behind it. -/
theorem cphase_d1_tail_raw (c : Conf) (hc : Reach c)
    (hC : c.q = .C)
    (hCzero : c.tape c.h = false)
    (hDone : c.tape (c.h-1) = true)
    (hzero1 : c.tape (c.h+1) = false)
    (hzero2 : c.tape (c.h+2) = false) :
    ∃ bout, shuttleRun 6 c = some bout ∧ Reach bout ∧
      BZero bout ∧ bout.h = c.h+2 ∧
      bout.tape (c.h-1) = true ∧
      bout.tape c.h = true ∧
      bout.tape (c.h+1) = true ∧
      (∀ x : Int, x ≤ c.h-2 → bout.tape x = c.tape x) := by
  let d : Conf := ⟨.D,c.h-1,setBit c.tape c.h true⟩
  let f : Conf := ⟨.F,c.h,setBit d.tape (c.h-1) true⟩
  let d2 : Conf := ⟨.D,c.h+1,setBit f.tape c.h false⟩
  let e : Conf := ⟨.E,c.h,setBit d2.tape (c.h+1) false⟩
  let a : Conf := ⟨.A,c.h+1,setBit e.tape c.h true⟩
  let bout : Conf := ⟨.B,c.h+2,setBit a.tape (c.h+1) true⟩
  have hCstep : next c = some d := by simp [next,hC,hCzero,d]
  have hDread' : setBit c.tape c.h true (c.h-1) = true := by
    simp [setBit,show c.h-1 ≠ c.h by omega,hDone]
  have hDstep : next d = some f := by simp [next,d,f,hDread']
  have hFread' : setBit d.tape (c.h-1) true c.h = true := by
    simp [setBit,show c.h ≠ c.h-1 by omega,d,setBit]
  have hFstep : next f = some d2 := by simp [next,f,d2,hFread']
  have hD0read' : setBit f.tape c.h false (c.h+1) = false := by
    simp [setBit,show c.h+1 ≠ c.h by omega,
      f,setBit,show c.h+1 ≠ c.h-1 by omega,
      d,setBit,show c.h+1 ≠ c.h by omega,hzero1]
  have hD0step : next d2 = some e := by simp [next,d2,e,hD0read']
  have hEread' : setBit d2.tape (c.h+1) false c.h = false := by
    simp [d2,setBit,show c.h ≠ c.h+1 by omega]
  have hEstep : next e = some a := by simp [next,e,a,hEread']
  have hAread' : setBit e.tape c.h true (c.h+1) = false := by
    simp [e,d2,setBit,show c.h+1 ≠ c.h by omega]
  have hAstep : next a = some bout := by
    have hpos : c.h+1+1 = c.h+2 := by omega
    simp [next,a,bout,hAread',hpos]
  have hBread : bout.tape bout.h = false := by
    change setBit a.tape (c.h+1) true (c.h+2) = false
    simp [bout,a,e,d2,f,d,setBit,
      show c.h+2 ≠ c.h+1 by omega,
      show c.h+2 ≠ c.h by omega,
      show c.h+2 ≠ c.h-1 by omega,hzero2]
  have hrun : shuttleRun 6 c = some bout := by
    simp [shuttleRun,hCstep,hDstep,hFstep,hD0step,hEstep,hAstep]
  have hreach : Reach bout :=
    Reach.follow (Reach.follow (Reach.follow (Reach.follow (Reach.follow
      (Reach.follow hc hCstep) hDstep) hFstep) hD0step) hEstep) hAstep
  have hBzero : BZero bout := ⟨rfl,hBread⟩
  have htail_left : ∀ x : Int, x ≤ c.h-2 → bout.tape x = c.tape x := by
    intro x hx
    simp [bout,a,e,d2,f,d,setBit,
      show x ≠ c.h+1 by omega,
      show x ≠ c.h by omega,
      show x ≠ c.h-1 by omega]
  have hleftFinal : bout.tape (c.h-1) = true := by
    simp [bout,a,e,d2,f,d,setBit,
      show c.h-1 ≠ c.h+1 by omega,
      show c.h-1 ≠ c.h by omega]
  have hcenterFinal : bout.tape c.h = true := by
    simp [bout,a,e,d2,f,d,setBit,
      show c.h ≠ c.h+1 by omega]
  have hrightFinal : bout.tape (c.h+1) = true := by
    simp [bout,a,e,d2,f,d,setBit]
  exact ⟨bout,hrun,hreach,hBzero,rfl,hleftFinal,hcenterFinal,hrightFinal,htail_left⟩

/-- A finite alternating B0 ladder always reaches the C/0 110 gate.
    No global NoLeft4 shield is assumed; the proof explicitly carries the
    marker through each raw C/D/F/A/B retreat. -/
theorem markerB0Pattern_to_CGate (m : Nat) (b : Conf)
    (hb : Reach b) (hp : MarkerB0Pattern m b) :
    ∃ c, Reach c ∧ CGate c := by
  revert b hb hp
  induction m with
  | zero =>
      intro b hb hp
      have hscan : ∀ i : Nat, i < 3 →
          b.tape (b.h-1-(i:Int)) = true := by
        intro i hi
        have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi' with h | h | h
        · subst i
          simpa using hp.left1
        · subst i
          simpa [sub_sub_int] using hp.left2
        · subst i
          simpa [sub_sub_int] using hp.left3
      obtain ⟨c,hrun,hc,hphase,hzeros⟩ :=
        scan_from_B_exact b hb hp.hB 3 hscan
      rcases hphase with ⟨_,hC,hpos,hpres,_⟩
      have hpos' : c.h = b.h-4 := by omega
      have hCG : CGate c := by
        refine ⟨hC, ?_, ?_, ?_, ?_⟩
        · calc
            c.tape c.h = b.tape c.h := hpres c.h (by omega)
            _ = b.tape (b.h-4) := by rw [hpos']
            _ = false := by simpa [sub_sub_int] using hp.final0
        · have hx : c.h-1 = b.h-5 := by rw [hpos']; omega
          calc
            c.tape (c.h-1) = b.tape (c.h-1) := hpres (c.h-1) (by omega)
            _ = b.tape (b.h-5) := by rw [hx]
            _ = false := by simpa [sub_sub_int] using hp.final00
        · have hx : c.h-2 = b.h-6 := by rw [hpos']; omega
          calc
            c.tape (c.h-2) = b.tape (c.h-2) := hpres (c.h-2) (by omega)
            _ = b.tape (b.h-6) := by rw [hx]
            _ = true := by simpa [sub_sub_int] using hp.final1
        · have hx : c.h-3 = b.h-7 := by rw [hpos']; omega
          calc
            c.tape (c.h-3) = b.tape (c.h-3) := hpres (c.h-3) (by omega)
            _ = b.tape (b.h-7) := by rw [hx]
            _ = true := by simpa [sub_sub_int] using hp.final11
      exact ⟨c,hc,hCG⟩
  | succ m ih =>
      intro b hb hp
      have hscan : ∀ i : Nat, i < 3 →
          b.tape (b.h-1-(i:Int)) = true := by
        intro i hi
        have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi' with h | h | h
        · subst i
          simpa using hp.left1
        · subst i
          simpa [sub_sub_int] using hp.left2
        · subst i
          simpa [sub_sub_int] using hp.left3
      obtain ⟨c,hrun,hc,hphase,hzeros⟩ :=
        scan_from_B_exact b hb hp.hB 3 hscan
      rcases hphase with ⟨_,hC,hpos,hpres,_⟩
      have hpos' : c.h = b.h-4 := by omega
      have hzero0 : b.tape (b.h-4) = false := by
        simpa [sub_sub_int] using (hp.alternating 0 (by omega)).1
      have hdone0 : b.tape (b.h-5) = true := by
        simpa [sub_sub_int] using (hp.alternating 0 (by omega)).2
      have hczero : c.tape c.h = false := by
        calc
          c.tape c.h = b.tape c.h := hpres c.h (by omega)
          _ = b.tape (b.h-4) := by rw [hpos']
          _ = false := hzero0
      have hdone : c.tape (c.h-1) = true := by
        have hx : c.h-1 = b.h-5 := by rw [hpos']; omega
        calc
          c.tape (c.h-1) = b.tape (c.h-1) := hpres (c.h-1) (by omega)
          _ = b.tape (b.h-5) := by rw [hx]
          _ = true := hdone0
      have hzero1 : c.tape (c.h+1) = false := by
        have hz := hzeros 2 (by omega)
        have hx : c.h+1 = b.h-1-(2:Int) := by rw [hpos']; omega
        rw [hx]
        exact hz
      have hzero2 : c.tape (c.h+2) = false := by
        have hz := hzeros 1 (by omega)
        have hx : c.h+2 = b.h-1-(1:Int) := by rw [hpos']; omega
        rw [hx]
        exact hz
      obtain ⟨b',hret,hb',hB',hh',hleft,hcenter,hright,hpres2⟩ :=
        cphase_d1_tail_raw c hc hC hczero hdone hzero1 hzero2
      have hkeep (x : Int) (hx : x ≤ c.h-2) : b'.tape x = b.tape x := by
        calc
          b'.tape x = c.tape x := hpres2 x hx
          _ = b.tape x := hpres x (by omega)
      have hpat' : MarkerB0Pattern m b' := by
        refine ⟨hB', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have hx : b'.h-1 = c.h+1 := by rw [hh']; omega
          rw [hx]
          exact hright
        · have hx : b'.h-2 = c.h := by rw [hh']; omega
          rw [hx]
          exact hcenter
        · have hx : b'.h-3 = c.h-1 := by rw [hh']; omega
          rw [hx]
          exact hleft
        · intro i hi
          constructor
          · have hx : b'.h-4-2*(i:Int) =
                b.h-6-2*(i:Int) := by rw [hh',hpos']; omega
            rw [hx]
            rw [hkeep _ (by rw [hpos']; omega)]
            have hsrc := (hp.alternating (i+1) (by omega)).1
            have heq : b.h-6-2*(i:Int) =
                b.h-4-2*((i+1):Int) := by omega
            rw [heq]
            exact hsrc
          · have hx : b'.h-5-2*(i:Int) =
                b.h-7-2*(i:Int) := by rw [hh',hpos']; omega
            rw [hx]
            rw [hkeep _ (by rw [hpos']; omega)]
            have hsrc := (hp.alternating (i+1) (by omega)).2
            have heq : b.h-7-2*(i:Int) =
                b.h-5-2*((i+1):Int) := by omega
            rw [heq]
            exact hsrc
        · have hx : b'.h-4-2*(m:Int) =
              b.h-4-2*((m+1):Int) := by rw [hh']; omega
          rw [hx]
          rw [hkeep _ (by rw [hpos']; omega)]
          exact hp.final0
        · have hx : b'.h-5-2*(m:Int) =
              b.h-5-2*((m+1):Int) := by rw [hh']; omega
          rw [hx]
          rw [hkeep _ (by rw [hpos']; omega)]
          exact hp.final00
        · have hx : b'.h-6-2*(m:Int) =
              b.h-6-2*((m+1):Int) := by rw [hh']; omega
          rw [hx]
          rw [hkeep _ (by rw [hpos']; omega)]
          exact hp.final1
        · have hx : b'.h-7-2*(m:Int) =
              b.h-7-2*((m+1):Int) := by rw [hh']; omega
          rw [hx]
          rw [hkeep _ (by rw [hpos']; omega)]
          exact hp.final11
      exact ih b' hb' hpat'

#print axioms BB6Root119.cphase_d1_tail_raw
#print axioms BB6Root119.markerB0Pattern_to_CGate

end BB6Root119
