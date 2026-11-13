import Root119ZeroLeftCPhaseEdge

set_option linter.unusedSimpArgs false

namespace BB6Root119

def cphaseD1StepTape (t : Int → Bool) (h : Int) : Int → Bool :=
  let t1 := setBit t h true
  let t2 := setBit t1 (h-1) false
  let t3 := setBit t2 (h-2) false
  let t4 := setBit t3 (h-3) false
  let t5 := setBit t4 (h-4) true
  let t6 := setBit t5 (h-5) true
  let t7 := setBit t6 (h-4) false
  let t8 := setBit t7 (h-3) false
  let t9 := setBit t8 (h-4) true
  setBit t9 (h-3) true

theorem cphaseD1StepTape_local (t : Int → Bool) (h : Int) :
    cphaseD1StepTape t h (h-5) = true ∧
    cphaseD1StepTape t h (h-4) = true ∧
    cphaseD1StepTape t h (h-3) = true ∧
    cphaseD1StepTape t h (h-2) = false ∧
    cphaseD1StepTape t h (h-1) = false ∧
    cphaseD1StepTape t h h = true := by
  simp [cphaseD1StepTape, setBit]

theorem cphaseD1StepTape_left_exterior (t : Int → Bool) (h x : Int)
    (hx : x ≤ h-6) :
    cphaseD1StepTape t h x = t x := by
  simp [cphaseD1StepTape, setBit,
    show x ≠ h by omega, show x ≠ h-1 by omega,
    show x ≠ h-2 by omega, show x ≠ h-3 by omega,
    show x ≠ h-4 by omega, show x ≠ h-5 by omega]

theorem cphaseD1StepTape_right_exterior (t : Int → Bool) (h x : Int)
    (hx : h+1 ≤ x) :
    cphaseD1StepTape t h x = t x := by
  simp [cphaseD1StepTape, setBit,
    show x ≠ h by omega, show x ≠ h-1 by omega,
    show x ≠ h-2 by omega, show x ≠ h-3 by omega,
    show x ≠ h-4 by omega, show x ≠ h-5 by omega]

theorem b0_cphase_d1_r3_step (b : Conf) (hb : Reach b)
    (hB : b.q = .B) (h0 : b.tape b.h = false)
    (hscan : ∀ i : Nat, i < 3 →
      b.tape (b.h-1-(i:Int)) = true)
    (hzeroC : b.tape (b.h-4) = false)
    (honeD : b.tape (b.h-5) = true)
    (hshield : NoLeft4 true true false b) :
    ∃ bout, shuttleRun 10 b = some bout ∧ Reach bout ∧ BZero bout ∧
      bout.h = b.h-2 ∧ NoLeft4 true true false bout ∧
      bout.tape (b.h-3) = true ∧
      bout.tape (b.h-4) = true ∧
      bout.tape (b.h-5) = true ∧
      bout.tape (b.h-1) = false ∧
      bout.tape b.h = true ∧
      (∀ x : Int, x ≤ b.h-6 → bout.tape x = b.tape x) ∧
      (∀ x : Int, b.h+1 ≤ x → bout.tape x = b.tape x) := by
  rcases b with ⟨q,h,t⟩
  change q = .B at hB
  subst q
  change t h = false at h0
  have hscan0 : t (h-1) = true := by
    simpa using hscan 0 (by omega)
  have hscan1 : t (h-2) = true := by
    simpa using hscan 1 (by omega)
  have hscan2 : t (h-3) = true := by
    simpa using hscan 2 (by omega)
  let t1 : Int → Bool := setBit t h true
  let t2 : Int → Bool := setBit t1 (h-1) false
  let t3 : Int → Bool := setBit t2 (h-2) false
  let t4 : Int → Bool := setBit t3 (h-3) false
  let t5 : Int → Bool := setBit t4 (h-4) true
  let t6 : Int → Bool := setBit t5 (h-5) true
  let t7 : Int → Bool := setBit t6 (h-4) false
  let t8 : Int → Bool := setBit t7 (h-3) false
  let t9 : Int → Bool := setBit t8 (h-4) true
  let t10 : Int → Bool := cphaseD1StepTape t h
  have hread2 : t1 (h-1) = true := by
    simp [t1, setBit, show h-1 ≠ h by omega, hscan0]
  have hread3 : t2 (h-2) = true := by
    simp [t2, t1, setBit, show h-2 ≠ h by omega,
      show h-2 ≠ h-1 by omega, hscan1]
  have hread4 : t3 (h-3) = true := by
    simp [t3, t2, t1, setBit, show h-3 ≠ h by omega,
      show h-3 ≠ h-1 by omega, show h-3 ≠ h-2 by omega, hscan2]
  have hread5 : t4 (h-4) = false := by
    simp [t4, t3, t2, t1, setBit,
      show h-4 ≠ h by omega, show h-4 ≠ h-1 by omega,
      show h-4 ≠ h-2 by omega, show h-4 ≠ h-3 by omega, hzeroC]
  have hread6 : t5 (h-5) = true := by
    simp [t5, t4, t3, t2, t1, setBit,
      show h-5 ≠ h by omega, show h-5 ≠ h-1 by omega,
      show h-5 ≠ h-2 by omega, show h-5 ≠ h-3 by omega,
      show h-5 ≠ h-4 by omega, honeD]
  have hread7 : t6 (h-4) = true := by
    simp [t6, t5, setBit, show h-4 ≠ h-5 by omega]
  have hread8 : t7 (h-3) = false := by
    simp [t7, t6, t5, t4, t3, t2, t1, setBit,
      show h-3 ≠ h by omega, show h-3 ≠ h-1 by omega,
      show h-3 ≠ h-2 by omega, show h-3 ≠ h-4 by omega,
      show h-3 ≠ h-5 by omega]
  have hread9 : t8 (h-4) = false := by
    simp [t8, t7, setBit, show h-4 ≠ h-3 by omega]
  have hread10 : t9 (h-3) = false := by
    simp [t9, t8, setBit, show h-3 ≠ h-4 by omega]
  have ht10 : t10 = setBit t9 (h-3) true := by
    rfl
  let c1 : Conf := ⟨.C,h-1,t1⟩
  let c2 : Conf := ⟨.C,h-2,t2⟩
  let c3 : Conf := ⟨.C,h-3,t3⟩
  let c4 : Conf := ⟨.C,h-4,t4⟩
  let d : Conf := ⟨.D,h-5,t5⟩
  let f : Conf := ⟨.F,h-4,t6⟩
  let d2 : Conf := ⟨.D,h-3,t7⟩
  let e : Conf := ⟨.E,h-4,t8⟩
  let a : Conf := ⟨.A,h-3,t9⟩
  let rawBout : Conf := ⟨.B,h-2,t10⟩
  have h01 : h-1-1 = h-2 := by omega
  have h12 : h-2-1 = h-3 := by omega
  have h23 : h-3-1 = h-4 := by omega
  have h34 : h-4-1 = h-5 := by omega
  have h45 : h-5+1 = h-4 := by omega
  have h56 : h-4+1 = h-3 := by omega
  have h67 : h-3-1 = h-4 := by omega
  have h78 : h-4+1 = h-3 := by omega
  have h89 : h-3+1 = h-2 := by omega
  have hs1 : next ⟨.B,h,t⟩ = some c1 := by
    simp [next, h0, c1, t1]
  have hs2 : next c1 = some c2 := by
    simp [next, c1, c2, t2, t1, hread2, h01]
  have hs3 : next c2 = some c3 := by
    simp [next, c2, c3, t3, t2, hread3, h12]
  have hs4 : next c3 = some c4 := by
    simp [next, c3, c4, t4, t3, hread4, h23]
  have hs5 : next c4 = some d := by
    simp [next, c4, d, t5, t4, hread5, h34]
  have hs6 : next d = some f := by
    simp [next, d, f, t6, t5, hread6, h45]
  have hs7 : next f = some d2 := by
    simp [next, f, d2, t7, t6, hread7, h56]
  have hs8 : next d2 = some e := by
    simp [next, d2, e, t8, t7, hread8, h67]
  have hs9 : next e = some a := by
    simp [next, e, a, t9, t8, hread9, h78]
  have hs10 : next a = some rawBout := by
    simp [next, a, rawBout, t10, t9, ht10, hread10, h89]
  have hrawRun : shuttleRun 10 ⟨.B,h,t⟩ = some rawBout := by
    simp [shuttleRun, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10]
  have hBzero : BZero ⟨.B,h,t⟩ := ⟨rfl,h0⟩
  obtain ⟨sourceBout, hsourceRun, hsourceReach, hsourceBZero,
      hsourceHead, hsourceShield, _⟩ :=
    b0_cphase_d1_zero_wave_return ⟨.B,h,t⟩ 3 hb hBzero
      (by omega) hscan hzeroC honeD hshield
  have hsourceRun10 : shuttleRun 10 ⟨.B,h,t⟩ = some sourceBout := by
    simpa using hsourceRun
  have heq : rawBout = sourceBout :=
    Option.some.inj (hrawRun.symm.trans hsourceRun10)
  have hreachRaw : Reach rawBout := by
    rw [heq]
    exact hsourceReach
  have hBzeroRaw : BZero rawBout := by
    rw [heq]
    exact hsourceBZero
  have hshieldRaw : NoLeft4 true true false rawBout := by
    rw [heq]
    exact hsourceShield
  have hheadRaw : rawBout.h = h-2 := rfl
  have hlocal := cphaseD1StepTape_local t h
  have hleft1 : rawBout.tape (h-3) = true := by
    change cphaseD1StepTape t h (h-3) = true
    exact hlocal.2.2.1
  have hleft2 : rawBout.tape (h-4) = true := by
    change cphaseD1StepTape t h (h-4) = true
    exact hlocal.2.1
  have hleft3 : rawBout.tape (h-5) = true := by
    change cphaseD1StepTape t h (h-5) = true
    exact hlocal.1
  have hright1 : rawBout.tape (h-1) = false := by
    change cphaseD1StepTape t h (h-1) = false
    exact hlocal.2.2.2.2.1
  have hright2 : rawBout.tape h = true := by
    change cphaseD1StepTape t h h = true
    exact hlocal.2.2.2.2.2
  have hleftExterior : ∀ x : Int, x ≤ h-6 → rawBout.tape x = t x := by
    intro x hx
    exact cphaseD1StepTape_left_exterior t h x hx
  have hrightExterior : ∀ x : Int, h+1 ≤ x → rawBout.tape x = t x := by
    intro x hx
    exact cphaseD1StepTape_right_exterior t h x hx
  refine ⟨rawBout,hrawRun,hreachRaw,hBzeroRaw,hheadRaw,hshieldRaw,
    hleft1,hleft2,hleft3,hright1,hright2,hleftExterior,hrightExterior⟩

theorem zeroLeftEvenOutTape_cphaseD1_corridor
    (n : Nat) (t : Int → Bool) (h : Int) :
    ∀ i : Nat, i ≤ n →
      zeroLeftEvenOutTape n t h
        (h+2*(n:Int)-2*(i:Int)-2) = false ∧
      zeroLeftEvenOutTape n t h
        (h+2*(n:Int)-2*(i:Int)-3) = true := by
  intro i hi
  by_cases hlast : i = n
  · subst i
    have hidx1 : h+2*(n:Int)-2*(n:Int)-2 = h-2 := by omega
    have hidx2 : h+2*(n:Int)-2*(n:Int)-3 = h-3 := by omega
    rw [hidx1,hidx2]
    exact ⟨zeroLeftEvenOutTape_hm2 n t h, zeroLeftEvenOutTape_hm3 n t h⟩
  · have hilt : i < n := by omega
    let k : Nat := n-1-i
    have hk : k < n := by dsimp [k]; omega
    have hidx1 : h+2*(n:Int)-2*(i:Int)-2 = h+2*(k:Int) := by
      dsimp [k]
      omega
    have hidx2 : h+2*(n:Int)-2*(i:Int)-3 = h+2*(k:Int)-1 := by
      dsimp [k]
      omega
    rw [hidx1,hidx2]
    by_cases hk0 : k = 0
    · subst k
      have hnpos : 0 < n := by omega
      exact ⟨zeroLeftEvenOutTape_h_false n t h hnpos,
        zeroLeftEvenOutTape_hm1 n t h⟩
    · have hkpos : 0 < k := by omega
      let j : Nat := k-1
      have hj : j < n := by dsimp [j]; omega
      let fTape : Int → Bool := setBit (zeroLeftPrefixTape t h) h false
      have hF := evenSweepTape_oddCell n fTape (h+1) j hj
      have hD := evenSweepTape_evenCell n fTape (h+1) j hj
      have hidxF : h+2*(k:Int) = (h+1)+2*(j:Int)+1 := by
        dsimp [j]
        omega
      have hidxD : h+2*(k:Int)-1 = (h+1)+2*(j:Int) := by
        dsimp [j]
        omega
      have htermF1 : h+2*(k:Int) ≠ h+2*(n:Int) := by omega
      have htermF2 : h+2*(k:Int) ≠ h+2*(n:Int)+1 := by omega
      have htermD1 : h+2*(k:Int)-1 ≠ h+2*(n:Int) := by omega
      have htermD2 : h+2*(k:Int)-1 ≠ h+2*(n:Int)+1 := by omega
      have hFout : zeroLeftEvenOutTape n t h (h+2*(k:Int)) =
          evenSweepTape n fTape (h+1) (h+2*(k:Int)) := by
        simp [zeroLeftEvenOutTape,evenSweepB0Tape,fTape,setBit,
          htermF1,htermF2]
      have hDout : zeroLeftEvenOutTape n t h (h+2*(k:Int)-1) =
          evenSweepTape n fTape (h+1) (h+2*(k:Int)-1) := by
        simp [zeroLeftEvenOutTape,evenSweepB0Tape,fTape,setBit,
          htermD1,htermD2]
      rw [hFout,hidxF,hDout,hidxD]
      exact ⟨hF,hD⟩

theorem cphaseD1_repeat (m : Nat) (b : Conf)
    (hb : Reach b) (hBzero : BZero b)
    (hscan : ∀ i : Nat, i < 3 →
      b.tape (b.h-1-(i:Int)) = true)
    (hpairs : ∀ i : Nat, i < m →
      b.tape (b.h-4-2*(i:Int)) = false ∧
      b.tape (b.h-5-2*(i:Int)) = true)
    (hshield : NoLeft4 true true false b) :
    ∃ bout, shuttleRun (10*m) b = some bout ∧ Reach bout ∧
      BZero bout ∧ bout.h = b.h-2*(m:Int) ∧
      NoLeft4 true true false bout ∧
      bout.tape (bout.h-1) = true ∧
      bout.tape (bout.h-2) = true ∧
      bout.tape (bout.h-3) = true ∧
      (∀ x : Int, x ≤ bout.h-4 → bout.tape x = b.tape x) ∧
      (∀ x : Int, b.h+1 ≤ x → bout.tape x = b.tape x) ∧
      (∀ j : Nat, j < m →
        bout.tape (bout.h+1+2*(j:Int)) = false ∧
        bout.tape (bout.h+2+2*(j:Int)) = true) := by
  revert b hb hBzero hscan hpairs hshield
  induction m with
  | zero =>
    intro b hb hBzero hscan hpairs hshield
    refine ⟨b, by simp [shuttleRun], hb, hBzero, by simp,
      hshield, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h0 := hscan 0 (by omega)
      simpa using h0
    · have h1 := hscan 1 (by omega)
      simpa using h1
    · have h2 := hscan 2 (by omega)
      simpa using h2
    · intro x hx
      rfl
    · intro x hx
      rfl
    · intro j hj
      omega
  | succ m ih =>
    intro b hb hBzero hscan hpairs hshield
    rcases hBzero with ⟨hB,h0⟩
    have hpair0 := hpairs 0 (by omega)
    obtain ⟨b1,hstep,hb1,hB1,hhead1,hshield1,
      hleft1,hleft2,hleft3,hright1,hright2,hpresLeft1,hpresRight1⟩ :=
      b0_cphase_d1_r3_step b hb hB h0 hscan hpair0.1 hpair0.2 hshield
    have hscan1 : ∀ i : Nat, i < 3 →
        b1.tape (b1.h-1-(i:Int)) = true := by
      intro i hi
      have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hcases with hi0 | hi1 | hi2
      · subst i
        simpa [hhead1] using hleft1
      · subst i
        simpa [hhead1] using hleft2
      · subst i
        simpa [hhead1] using hleft3
    have hpairs1 : ∀ i : Nat, i < m →
        b1.tape (b1.h-4-2*(i:Int)) = false ∧
        b1.tape (b1.h-5-2*(i:Int)) = true := by
      intro i hi
      have hsource := hpairs (i+1) (by omega)
      have hidx1 : b1.h-4-2*(i:Int) =
          b.h-4-2*((i+1):Int) := by rw [hhead1]; omega
      have hidx2 : b1.h-5-2*(i:Int) =
          b.h-5-2*((i+1):Int) := by rw [hhead1]; omega
      have hleftBound : b.h-4-2*((i+1):Int) ≤ b.h-6 := by omega
      have hleftBound' : b.h-5-2*((i+1):Int) ≤ b.h-6 := by omega
      constructor
      · rw [hidx1]
        exact (hpresLeft1 _ hleftBound).trans hsource.1
      · rw [hidx2]
        exact (hpresLeft1 _ hleftBound').trans hsource.2
    obtain ⟨bout,hrun2,hbout,hBOut,hheadOut,hshieldOut,
      hleftOut1,hleftOut2,hleftOut3,hpresLeft2,hpresRight2,hcorr2⟩ :=
      ih b1 hb1 hB1 hscan1 hpairs1 hshield1
    have hlen : 10*(m+1) = 10 + 10*m := by omega
    have hrun : shuttleRun (10*(m+1)) b = some bout := by
      rw [hlen,shuttleRun_add,hstep]
      simpa using hrun2
    have hhead : bout.h = b.h-2*((m+1):Int) := by
      rw [hheadOut,hhead1]
      omega
    have hpresLeft : ∀ x : Int, x ≤ bout.h-4 → bout.tape x = b.tape x := by
      intro x hx
      have hx1 : x ≤ b.h-6 := by rw [hhead] at hx; omega
      exact (hpresLeft2 x hx).trans (hpresLeft1 x hx1)
    have hpresRight : ∀ x : Int, b.h+1 ≤ x → bout.tape x = b.tape x := by
      intro x hx
      have hx1 : b1.h+1 ≤ x := by rw [hhead1]; omega
      exact (hpresRight2 x hx1).trans (hpresRight1 x hx)
    have hcorr : ∀ j : Nat, j < m+1 →
        bout.tape (bout.h+1+2*(j:Int)) = false ∧
        bout.tape (bout.h+2+2*(j:Int)) = true := by
      intro j hj
      by_cases hjlast : j = m
      · subst j
        have hidx1 : bout.h+1+2*(m:Int) = b.h-1 := by
          rw [hhead]
          omega
        have hidx2 : bout.h+2+2*(m:Int) = b.h := by
          rw [hhead]
          omega
        constructor
        · rw [hidx1]
          calc
            bout.tape (b.h-1) = b1.tape (b.h-1) :=
              hpresRight2 (b.h-1) (by rw [hhead1]; omega)
            _ = b1.tape (b1.h+1) := by
              congr 1
              rw [hhead1]
              omega
            _ = false := hright1
        · rw [hidx2]
          calc
            bout.tape b.h = b1.tape b.h :=
              hpresRight2 b.h (by rw [hhead1]; omega)
            _ = b1.tape (b1.h+2) := by
              congr 1
              rw [hhead1]
              omega
            _ = true := hright2
      · have hjlt : j < m := by omega
        exact hcorr2 j hjlt
    refine ⟨bout,hrun,hbout,hBOut,hhead,hshieldOut,
      hleftOut1,hleftOut2,hleftOut3,hpresLeft,hpresRight,hcorr⟩

theorem zeroLeftEven_full_return (n : Nat) (b : Conf)
    (hb : Reach b)
    (hB : b.q = .B) (h0 : b.tape b.h = false)
    (h1 : b.tape (b.h-1) = false)
    (h2 : b.tape (b.h-2) = false)
    (h3 : b.tape (b.h-3) = false)
    (hones : ∀ j : Nat, j < 2*n →
      b.tape (b.h+1+(j:Int)) = true)
    (hzero : b.tape (b.h+2*(n:Int)+1) = false)
    (hzeroNext : b.tape (b.h+2*(n:Int)+2) = false)
    (hshield : NoLeft4 true true false b) :
    ∃ bout, shuttleRun (12*n+22) b = some bout ∧ Reach bout ∧
      BZero bout ∧ bout.h = b.h ∧
      NoLeft4 true true false bout ∧
      bout.tape (b.h-1) = true ∧
      bout.tape (b.h-2) = true ∧
      bout.tape (b.h-3) = true ∧
      (∀ j : Nat, j ≤ n →
        bout.tape (b.h+1+2*(j:Int)) = false ∧
        bout.tape (b.h+2+2*(j:Int)) = true) ∧
      (∀ x : Int, x ≤ b.h-4 → bout.tape x = b.tape x) ∧
      (∀ x : Int, b.h+2*(n:Int)+3 ≤ x → bout.tape x = b.tape x) := by
  let d : Conf := ⟨.B,b.h+2*(n:Int)+2,zeroLeftEvenOutTape n b.tape b.h⟩
  have hfirst : shuttleRun (2*n+12) b = some d := by
    simpa [d] using zeroLeftEvenRun_exact n b hB h0 h1 h2 h3
      hones hzero hzeroNext
  have hdReach : Reach d :=
    shuttleRun_reachable (2*n+12) b d hb hfirst
  have hdB : BZero d := by
    refine ⟨rfl,?_⟩
    change zeroLeftEvenOutTape n b.tape b.h
      (b.h+2*(n:Int)+2) = false
    exact zeroLeftEvenOutTape_head n b.tape b.h hzeroNext
  have hshieldTape : NoLeft1100 b.tape b.h := by
    intro x hx hw
    exact hshield x hx hw
  have hdShieldTape :=
    zeroLeftEvenOutTape_preserves_NoLeft1100 n b.tape b.h hshieldTape
  have hdShield : NoLeft4 true true false d := by
    intro x hx hw
    exact hdShieldTape x hx hw
  have hpat := zeroLeftEvenOutTape_cphaseD1_pattern n b.tape b.h
  have hdScan : ∀ i : Nat, i < 3 →
      d.tape (d.h-1-(i:Int)) = true := by
    intro i hi
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hcases with hi0 | hi1 | hi2
    · subst i
      have hidx : d.h-1-((0:Nat):Int) = b.h+2*(n:Int)+1 := by
        dsimp [d]
        omega
      rw [hidx]
      exact hpat.1
    · subst i
      have hidx : d.h-1-((1:Nat):Int) = b.h+2*(n:Int) := by
        dsimp [d]
        omega
      rw [hidx]
      exact hpat.2.1
    · subst i
      have hidx : d.h-1-((2:Nat):Int) = b.h+2*(n:Int)-1 := by
        dsimp [d]
        omega
      rw [hidx]
      exact hpat.2.2.1
  have hdPairs : ∀ i : Nat, i < n+1 →
      d.tape (d.h-4-2*(i:Int)) = false ∧
      d.tape (d.h-5-2*(i:Int)) = true := by
    intro i hi
    have hi' : i ≤ n := by omega
    have hpair := zeroLeftEvenOutTape_cphaseD1_corridor n b.tape b.h i hi'
    have hidx1 : d.h-4-2*(i:Int) =
        b.h+2*(n:Int)-2*(i:Int)-2 := by
      dsimp [d]
      omega
    have hidx2 : d.h-5-2*(i:Int) =
        b.h+2*(n:Int)-2*(i:Int)-3 := by
      dsimp [d]
      omega
    rw [hidx1,hidx2]
    exact hpair
  obtain ⟨bout,hrunRepeat,hbout,hBOut,hheadRepeat,hshieldOut,
      hleft1,hleft2,hleft3,hpresLeft,hpresRight,hcorr⟩ :=
    cphaseD1_repeat (n+1) d hdReach hdB hdScan hdPairs hdShield
  have hhead : bout.h = b.h := by
    rw [hheadRepeat]
    dsimp [d]
    omega
  have hlen : 12*n+22 = (2*n+12) + 10*(n+1) := by omega
  have hrun : shuttleRun (12*n+22) b = some bout := by
    rw [hlen,shuttleRun_add,hfirst]
    simpa using hrunRepeat
  have hleft : ∀ x : Int, x ≤ b.h-4 → bout.tape x = b.tape x := by
    intro x hx
    have hx' : x ≤ bout.h-4 := by rw [hhead]; exact hx
    calc
      bout.tape x = d.tape x := hpresLeft x hx'
      _ = b.tape x := by
        change zeroLeftEvenOutTape n b.tape b.h x = b.tape x
        exact zeroLeftEvenOutTape_left n b.tape b.h x hx
  have hright : ∀ x : Int, b.h+2*(n:Int)+3 ≤ x →
      bout.tape x = b.tape x := by
    intro x hx
    have hx' : d.h+1 ≤ x := by dsimp [d]; omega
    calc
      bout.tape x = d.tape x := hpresRight x hx'
      _ = b.tape x := by
        change zeroLeftEvenOutTape n b.tape b.h x = b.tape x
        exact zeroLeftEvenOutTape_right n b.tape b.h x (by dsimp [d]; omega)
  have hcorrFinal : ∀ j : Nat, j ≤ n →
      bout.tape (b.h+1+2*(j:Int)) = false ∧
      bout.tape (b.h+2+2*(j:Int)) = true := by
    intro j hj
    have hj' : j < n+1 := by omega
    have h := hcorr j hj'
    simpa [hhead] using h
  exact ⟨bout,hrun,hbout,hBOut,hhead,hshieldOut,
    (by simpa [hhead] using hleft1),
    (by simpa [hhead] using hleft2),
    (by simpa [hhead] using hleft3),
    hcorrFinal,hleft,hright⟩

#print axioms BB6Root119.b0_cphase_d1_r3_step
#print axioms BB6Root119.zeroLeftEvenOutTape_cphaseD1_corridor
#print axioms BB6Root119.cphaseD1_repeat
#print axioms BB6Root119.zeroLeftEven_full_return

end BB6Root119
