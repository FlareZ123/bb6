import Root119OddEvenChain
import Root119CPhaseReturn
import Root119AncestryTen
import Root119EvenExtra

set_option linter.unusedSimpArgs false

namespace BB6Root119

/-- A B/0 whose five-cell left suffix is 10111 cannot be the regular
    halting gate 1100 1^r. This is a suffix statement, not a global
    exclusion of 1100 elsewhere on the tape. -/
theorem not_BBad_of_suffix10111 (b : Conf)
    (h5 : b.tape (b.h-5) = true)
    (h4 : b.tape (b.h-4) = false)
    (h3 : b.tape (b.h-3) = true)
    (h2 : b.tape (b.h-2) = true)
    (h1 : b.tape (b.h-1) = true) :
    ¬ BBad b := by
  intro hbad
  rcases hbad with ⟨_,r,hones,hzero1,hzero2,_,_⟩
  have hcases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ 4 ≤ r := by omega
  rcases hcases with hr0 | hr1 | hr2 | hr3 | hr4
  · have hidx : b.h-1-(r:Int) = b.h-1 := by rw [hr0]; omega
    rw [hidx] at hzero1
    have hfalse : true = false := h1.symm.trans hzero1
    cases hfalse
  · have hidx : b.h-1-(r:Int) = b.h-2 := by rw [hr1]; omega
    rw [hidx] at hzero1
    have hfalse : true = false := h2.symm.trans hzero1
    cases hfalse
  · have hidx : b.h-1-(r:Int) = b.h-3 := by rw [hr2]; omega
    rw [hidx] at hzero1
    have hfalse : true = false := h3.symm.trans hzero1
    cases hfalse
  · have hidx : b.h-2-(r:Int) = b.h-5 := by rw [hr3]; omega
    rw [hidx] at hzero2
    have hfalse : true = false := h5.symm.trans hzero2
    cases hfalse
  · have htrue := hones 3 (by omega)
    have hidx : b.h-1-(3:Int) = b.h-4 := by omega
    rw [hidx] at htrue
    have hfalse : true = false := htrue.symm.trans h4
    cases hfalse

/-- The last seven cells of an even-sweep B/0 output are 1010111.
    The first five cells alone already exclude BBad; the extra two expose
    the zero/one barrier needed by the C-phase return. -/
theorem evenSweepBResultTape_last7 (m : Nat) (hm : 1 < m)
    (t : Int → Bool) (h : Int) :
    evenSweepBResultTape m t h (h+2*(m+1)-6) = true ∧
    evenSweepBResultTape m t h (h+2*(m+1)-5) = false ∧
    evenSweepBResultTape m t h (h+2*(m+1)-4) = true ∧
    evenSweepBResultTape m t h (h+2*(m+1)-3) = false ∧
    evenSweepBResultTape m t h (h+2*(m+1)-2) = true ∧
    evenSweepBResultTape m t h (h+2*(m+1)-1) = true ∧
    evenSweepBResultTape m t h (h+2*(m+1)) = true := by
  have hkeep (x : Int) (hx0 : x ≠ h+2*(m+1))
      (hx1 : x ≠ h+2*(m+1)-1) :
      evenSweepBResultTape m t h x = evenSweepTape (m+1) t h x := by
    simp [evenSweepBResultTape, setBit, hx0, hx1]
  have hidx6 : h+2*(m+1)-6 = h+2*((m-2:Nat):Int) := by omega
  have hidx5 : h+2*(m+1)-5 = h+2*((m-2:Nat):Int)+1 := by omega
  have hidx4 : h+2*(m+1)-4 = h+2*((m-1:Nat):Int) := by omega
  have hidx3 : h+2*(m+1)-3 = h+2*((m-1:Nat):Int)+1 := by omega
  have hidx2 : h+2*(m+1)-2 = h+2*(m:Int) := by omega
  have he6 : evenSweepTape (m+1) t h
      (h+2*((m-2:Nat):Int)) = true :=
    evenSweepTape_evenCell (m+1) t h (m-2) (by omega)
  have ho5 : evenSweepTape (m+1) t h
      (h+2*((m-2:Nat):Int)+1) = false :=
    evenSweepTape_oddCell (m+1) t h (m-2) (by omega)
  have he4 : evenSweepTape (m+1) t h
      (h+2*((m-1:Nat):Int)) = true :=
    evenSweepTape_evenCell (m+1) t h (m-1) (by omega)
  have ho3 : evenSweepTape (m+1) t h
      (h+2*((m-1:Nat):Int)+1) = false :=
    evenSweepTape_oddCell (m+1) t h (m-1) (by omega)
  have he2 : evenSweepTape (m+1) t h (h+2*(m:Int)) = true :=
    evenSweepTape_evenCell (m+1) t h m (by omega)
  have h6 : evenSweepBResultTape m t h (h+2*(m+1)-6) = true := by
    rw [hkeep _ (by omega) (by omega), hidx6]
    exact he6
  have h5 : evenSweepBResultTape m t h (h+2*(m+1)-5) = false := by
    rw [hkeep _ (by omega) (by omega), hidx5]
    exact ho5
  have h4 : evenSweepBResultTape m t h (h+2*(m+1)-4) = true := by
    rw [hkeep _ (by omega) (by omega), hidx4]
    exact he4
  have h3 : evenSweepBResultTape m t h (h+2*(m+1)-3) = false := by
    rw [hkeep _ (by omega) (by omega), hidx3]
    exact ho3
  have h2 : evenSweepBResultTape m t h (h+2*(m+1)-2) = true := by
    rw [hkeep _ (by omega) (by omega), hidx2]
    exact he2
  have h1 : evenSweepBResultTape m t h (h+2*(m+1)-1) = true := by
    have hp : h+2*(m+1)-1 ≠ h+2*(m+1) := by omega
    simp [evenSweepBResultTape, setBit, hp]
  have h0 : evenSweepBResultTape m t h (h+2*(m+1)) = true := by
    simp [evenSweepBResultTape, setBit]
  exact ⟨h6,h5,h4,h3,h2,h1,h0⟩

/-- A completed even-sweep B/0 endpoint is outside the exact regular
    halting gate, independently of its untouched exterior tape. -/
theorem evenSweepBResultTape_output_not_BBad (m : Nat) (hm : 0 < m)
    (t : Int → Bool) (h : Int) :
    ¬ BBad
      (⟨.B,h+2*(m+1)+1,evenSweepBResultTape m t h⟩ : Conf) := by
  let b : Conf := ⟨.B,h+2*(m+1)+1,evenSweepBResultTape m t h⟩
  have htail := evenSweepBResultTape_last7 m (by omega) t h
  have hidx5 : (h+2*(m+1)+1:Int)-5 = h+2*(m+1)-4 := by omega
  have hidx4 : (h+2*(m+1)+1:Int)-4 = h+2*(m+1)-3 := by omega
  have hidx3 : (h+2*(m+1)+1:Int)-3 = h+2*(m+1)-2 := by omega
  have hidx2 : (h+2*(m+1)+1:Int)-2 = h+2*(m+1)-1 := by omega
  have hidx1 : (h+2*(m+1)+1:Int)-1 = h+2*(m+1) := by omega
  have hb5 : b.tape (b.h-5) = true := by
    change evenSweepBResultTape m t h ((h+2*(m+1)+1:Int)-5) = true
    rw [hidx5]
    exact htail.2.2.1
  have hb4 : b.tape (b.h-4) = false := by
    change evenSweepBResultTape m t h ((h+2*(m+1)+1:Int)-4) = false
    rw [hidx4]
    exact htail.2.2.2.1
  have hb3 : b.tape (b.h-3) = true := by
    change evenSweepBResultTape m t h ((h+2*(m+1)+1:Int)-3) = true
    rw [hidx3]
    exact htail.2.2.2.2.1
  have hb2 : b.tape (b.h-2) = true := by
    change evenSweepBResultTape m t h ((h+2*(m+1)+1:Int)-2) = true
    rw [hidx2]
    exact htail.2.2.2.2.2.1
  have hb1 : b.tape (b.h-1) = true := by
    change evenSweepBResultTape m t h ((h+2*(m+1)+1:Int)-1) = true
    rw [hidx1]
    exact htail.2.2.2.2.2.2
  exact not_BBad_of_suffix10111 b hb5 hb4 hb3 hb2 hb1

/-- The six-step C-phase tail returns to B/0 and is BBad-free when the
    two cells immediately beyond its written 111 suffix are 01. No global
    1100-avoidance hypothesis is needed. -/
theorem cphase_d1_tail_barrier (c : Conf) (hc : Reach c)
    (hC : c.q = .C) (hCzero : c.tape c.h = false)
    (hDone : c.tape (c.h-1) = true)
    (hzero1 : c.tape (c.h+1) = false)
    (hzero2 : c.tape (c.h+2) = false)
    (hbarrier0 : c.tape (c.h-2) = false)
    (hbarrier1 : c.tape (c.h-3) = true) :
    ∃ bout, shuttleRun 6 c = some bout ∧ Reach bout ∧ BZero bout ∧
      bout.h = c.h+2 ∧
      (∀ x : Int, x ≤ c.h-2 → bout.tape x = c.tape x) ∧
      bout.tape (c.h-1) = true ∧ bout.tape c.h = true ∧
      bout.tape (c.h+1) = true ∧ ¬ BBad bout := by
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
  have hhead : bout.h = c.h+2 := rfl
  have hb5 : bout.tape (bout.h-5) = true := by
    have hidx : bout.h-5 = c.h-3 := by rw [hhead]; omega
    rw [hidx]
    calc
      bout.tape (c.h-3) = c.tape (c.h-3) :=
        htail_left (c.h-3) (by omega)
      _ = true := hbarrier1
  have hb4 : bout.tape (bout.h-4) = false := by
    have hidx : bout.h-4 = c.h-2 := by rw [hhead]; omega
    rw [hidx]
    calc
      bout.tape (c.h-2) = c.tape (c.h-2) :=
        htail_left (c.h-2) (by omega)
      _ = false := hbarrier0
  have hb3 : bout.tape (bout.h-3) = true := by
    have hidx : bout.h-3 = c.h-1 := by rw [hhead]; omega
    rw [hidx]
    exact hleftFinal
  have hb2 : bout.tape (bout.h-2) = true := by
    have hidx : bout.h-2 = c.h := by rw [hhead]; omega
    rw [hidx]
    exact hcenterFinal
  have hb1 : bout.tape (bout.h-1) = true := by
    have hidx : bout.h-1 = c.h+1 := by rw [hhead]; omega
    rw [hidx]
    exact hrightFinal
  exact ⟨bout,hrun,hreach,hBzero,hhead,htail_left,hleftFinal,hcenterFinal,hrightFinal,
    not_BBad_of_suffix10111 bout hb5 hb4 hb3 hb2 hb1⟩

/-- A B/0 C-phase return needs only a two-cell 01 barrier to exclude the
    exact regular halting gate; it does not need the global NoLeft4 shield. -/
theorem b0_cphase_d1_zero_wave_return_barrier (b : Conf) (r : Nat)
    (hb : Reach b) (hB : BZero b) (hr : 2 ≤ r)
    (hscan : ∀ i : Nat, i < r → b.tape (b.h-1-(i:Int)) = true)
    (hzeroC : b.tape (b.h-1-(r:Int)) = false)
    (honeD : b.tape (b.h-2-(r:Int)) = true)
    (hbarrier0 : b.tape (b.h-3-(r:Int)) = false)
    (hbarrier1 : b.tape (b.h-4-(r:Int)) = true) :
    ∃ bout, shuttleRun (r+7) b = some bout ∧ Reach bout ∧ BZero bout ∧
      bout.h = b.h-(r:Int)+1 ∧
      (∀ x : Int, x ≤ b.h-(r:Int)-3 → bout.tape x = b.tape x) ∧
      bout.tape (b.h-(r:Int)-2) = true ∧
      bout.tape (b.h-(r:Int)-1) = true ∧
      bout.tape (b.h-(r:Int)) = true ∧ ¬ BBad bout := by
  obtain ⟨c,hscanRun,hc,hphase,hzeros⟩ :=
    scan_from_B_exact b hb hB r hscan
  have hpos : c.h = b.h-1-(r:Int) := hphase.2.2.1
  have hprefix : ∀ x : Int, x ≤ c.h → c.tape x = b.tape x :=
    hphase.2.2.2.1
  have hC : c.q = .C := hphase.2.1
  have hCzero : c.tape c.h = false := by
    calc
      c.tape c.h = b.tape c.h := hprefix c.h (by omega)
      _ = b.tape (b.h-1-(r:Int)) := by rw [hpos]
      _ = false := hzeroC
  have hDone : c.tape (c.h-1) = true := by
    calc
      c.tape (c.h-1) = b.tape (c.h-1) := hprefix (c.h-1) (by omega)
      _ = b.tape (b.h-2-(r:Int)) := by rw [hpos]; congr 1 <;> omega
      _ = true := honeD
  have hzero1 : c.tape (c.h+1) = false := by
    have hidx : c.h+1 = b.h-1-((r-1:Nat):Int) := by rw [hpos]; omega
    rw [hidx]
    exact hzeros (r-1) (by omega)
  have hzero2 : c.tape (c.h+2) = false := by
    have hidx : c.h+2 = b.h-1-((r-2:Nat):Int) := by rw [hpos]; omega
    rw [hidx]
    exact hzeros (r-2) (by omega)
  have hbarrier0C : c.tape (c.h-2) = false := by
    have hidx : c.h-2 = b.h-3-(r:Int) := by rw [hpos]; omega
    calc
      c.tape (c.h-2) = b.tape (c.h-2) := hprefix (c.h-2) (by omega)
      _ = b.tape (b.h-3-(r:Int)) := by rw [hidx]
      _ = false := hbarrier0
  have hbarrier1C : c.tape (c.h-3) = true := by
    have hidx : c.h-3 = b.h-4-(r:Int) := by rw [hpos]; omega
    calc
      c.tape (c.h-3) = b.tape (c.h-3) := hprefix (c.h-3) (by omega)
      _ = b.tape (b.h-4-(r:Int)) := by rw [hidx]
      _ = true := hbarrier1
  obtain ⟨bout,htail,hbout,hBzero,hheadTail,hpresTail,
      hleftTail,hcenterTail,hrightTail,hnotBad⟩ :=
    cphase_d1_tail_barrier c hc hC hCzero hDone hzero1 hzero2
      hbarrier0C hbarrier1C
  have htime : r+7 = (r+1)+6 := by omega
  have hrun : shuttleRun (r+7) b = some bout := by
    rw [htime,shuttleRun_add,hscanRun]
    simp [htail]
  have hhead : bout.h = b.h-(r:Int)+1 := by
    rw [hheadTail,hpos]
    omega
  have hpres : ∀ x : Int, x ≤ b.h-(r:Int)-3 →
      bout.tape x = b.tape x := by
    intro x hx
    have hxC : x ≤ c.h-2 := by rw [hpos]; omega
    calc
      bout.tape x = c.tape x := hpresTail x hxC
      _ = b.tape x := hprefix x (by rw [hpos]; omega)
  have hleftOut : bout.tape (b.h-(r:Int)-2) = true := by
    have hidx : b.h-(r:Int)-2 = c.h-1 := by rw [hpos]; omega
    rw [hidx]
    exact hleftTail
  have hcenterOut : bout.tape (b.h-(r:Int)-1) = true := by
    have hidx : b.h-(r:Int)-1 = c.h := by rw [hpos]; omega
    rw [hidx]
    exact hcenterTail
  have hrightOut : bout.tape (b.h-(r:Int)) = true := by
    have hidx : b.h-(r:Int) = c.h+1 := by rw [hpos]; omega
    rw [hidx]
    exact hrightTail
  exact ⟨bout,hrun,hbout,hBzero,hhead,hpres,hleftOut,hcenterOut,hrightOut,hnotBad⟩

/-- The odd-even prefix followed by the C-phase D1 return is BBad-free
    for every genuine input. The old global 1100 shield and its sharp
    three-cell boundary guard are unnecessary: the even sweep supplies
    a persistent 01 separator immediately beyond the final 111 suffix. -/
theorem b0_odd_even_prefix_then_cphaseD1_safe (b : Conf) (n : Nat)
    (hb : Reach b) (hb0 : BZero b)
    (hleft : b.tape (b.h-1) = true)
    (hzero : b.tape (b.h-2) = false)
    (hone : b.tape (b.h-3) = true)
    (hones : ∀ j : Nat, j < 2*n → b.tape (b.h+1+(j:Int)) = true)
    (hterminal1 : b.tape (b.h+(2*n+1:Int)) = false)
    (hterminal2 : b.tape (b.h+(2*n+2:Int)) = false)
    (hfinal : b.tape (b.h+(2*n+3:Int)) = false) :
    ∃ bout, run (6*n+33) b = some bout ∧
      Reach bout ∧ BZero bout ∧ ¬ BBad bout := by
  have hn : 2 ≤ n := by
    by_contra hnot
    have hcases : n = 0 ∨ n = 1 := by omega
    obtain ⟨hr1,hr2,hr3,hr4⟩ :=
      reached_B0_left10x_right1111 b hb hb0.1 hb0.2 hzero hone
    rcases hcases with hn0 | hn1
    · have hfalse : b.tape (b.h+1) = false := by
        simpa [hn0] using hterminal1
      have hfalse' : true = false := hr1.symm.trans hfalse
      cases hfalse'
    · have hfalse : b.tape (b.h+3) = false := by
        simpa [hn1] using hterminal1
      have hfalse' : true = false := hr3.symm.trans hfalse
      cases hfalse'
  obtain ⟨b1,hrun1,hreach1,hB1,hhead1,htape1⟩ :=
    b0_odd_even_chain_to_b0_exact b n hb hb0 hleft hzero hone hones
      hterminal1 hterminal2 hfinal
  let tD2 : Int → Bool :=
    setBit (setBit (oddWaveTape n (twoWavePrefixTape b.tape b.h) (b.h-1))
      (b.h-2) true) (b.h-3) false
  have htape1' : b1.tape = evenSweepBResultTape (n+1) tD2 (b.h-2) := by
    simpa [tD2] using htape1
  have hhead1' : b1.h = (b.h-2)+2*((n+1)+1)+1 := by
    rw [hhead1]
    omega
  obtain ⟨hp6,hp5,hp4,hp3,hp2,hp1,hp0⟩ :=
    evenSweepBResultTape_last7 (n+1) (by omega) tD2 (b.h-2)
  have hscan : ∀ i : Nat, i < 3 →
      b1.tape (b1.h-1-(i:Int)) = true := by
    intro i hi
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hcases with hi0 | hi1 | hi2
    · subst i
      have hidx : b1.h-1-((0:Nat):Int) =
          (b.h-2)+2*((n+1)+1) := by rw [hhead1']; omega
      rw [htape1',hidx]
      exact hp0
    · subst i
      have hidx : b1.h-1-((1:Nat):Int) =
          (b.h-2)+2*((n+1)+1)-1 := by rw [hhead1']; omega
      rw [htape1',hidx]
      exact hp1
    · subst i
      have hidx : b1.h-1-((2:Nat):Int) =
          (b.h-2)+2*((n+1)+1)-2 := by rw [hhead1']; omega
      rw [htape1',hidx]
      exact hp2
  have hzeroC : b1.tape (b1.h-1-(3:Int)) = false := by
    have hidx : b1.h-1-(3:Int) =
        (b.h-2)+2*((n+1)+1)-3 := by rw [hhead1']; omega
    rw [htape1',hidx]
    exact hp3
  have honeD : b1.tape (b1.h-2-(3:Int)) = true := by
    have hidx : b1.h-2-(3:Int) =
        (b.h-2)+2*((n+1)+1)-4 := by rw [hhead1']; omega
    rw [htape1',hidx]
    exact hp4
  have hbarrier0 : b1.tape (b1.h-3-(3:Int)) = false := by
    have hidx : b1.h-3-(3:Int) =
        (b.h-2)+2*((n+1)+1)-5 := by rw [hhead1']; omega
    rw [htape1',hidx]
    exact hp5
  have hbarrier1 : b1.tape (b1.h-4-(3:Int)) = true := by
    have hidx : b1.h-4-(3:Int) =
        (b.h-2)+2*((n+1)+1)-6 := by rw [hhead1']; omega
    rw [htape1',hidx]
    exact hp6
  obtain ⟨bout,htail,hreach2,hB2,hhead2,_,_,_,_,hnotBad⟩ :=
    b0_cphase_d1_zero_wave_return_barrier b1 3 hreach1 hB1 (by omega)
      hscan hzeroC honeD hbarrier0 hbarrier1
  have hrun2 : run 10 b1 = some bout := by
    rw [run_eq_shuttleRun]
    exact htail
  have htime : 6*n+33 = (6*n+23)+10 := by omega
  have hrun : run (6*n+33) b = some bout := by
    rw [htime,run_add,hrun1]
    simp [hrun2]
  exact ⟨bout,hrun,hreach2,hB2,hnotBad⟩

#print axioms BB6Root119.not_BBad_of_suffix10111
#print axioms BB6Root119.evenSweepBResultTape_last7
#print axioms BB6Root119.cphase_d1_tail_barrier
#print axioms BB6Root119.b0_cphase_d1_zero_wave_return_barrier
#print axioms BB6Root119.b0_odd_even_prefix_then_cphaseD1_safe


/-- A B/0 state carrying the local C-phase D1 core and k further alternating
    (1,0) pairs to its left.  One ten-step C-phase return consumes one pair
    and reproduces the same core two cells to the left. -/
def CPhaseSeed (k : Nat) (b : Conf) : Prop :=
  (∀ i : Nat, i < 3 → b.tape (b.h-1-(i:Int)) = true) ∧
  b.tape (b.h-4) = false ∧
  b.tape (b.h-5) = true ∧
  (∀ j : Nat, j < k →
    b.tape (b.h-7-2*(j:Int)) = true ∧
    b.tape (b.h-6-2*(j:Int)) = false)

/-- One barrier-protected C-phase D1 return shifts the seed two cells left,
    consuming exactly its first alternating pair. -/
theorem cphase_seed_step (b : Conf) (k : Nat)
    (hb : Reach b) (hB : BZero b) (hk : 0 < k)
    (hseed : CPhaseSeed k b) :
    ∃ bout, shuttleRun 10 b = some bout ∧ Reach bout ∧ BZero bout ∧
      bout.h = b.h-2 ∧ CPhaseSeed (k-1) bout ∧ ¬ BBad bout := by
  rcases hseed with ⟨hscan,hzero,hone,hpairs⟩
  have hbarrier1 : b.tape (b.h-7) = true :=
    (hpairs 0 (by omega)).1
  have hbarrier0 : b.tape (b.h-6) = false :=
    (hpairs 0 (by omega)).2
  obtain ⟨bout,hrun,hreach,hBzero,hhead,hpres,hleftOut,
      hcenterOut,hrightOut,hnotBad⟩ :=
    b0_cphase_d1_zero_wave_return_barrier b 3 hb hB (by omega)
      hscan hzero hone hbarrier0 hbarrier1
  have hhead' : bout.h = b.h-2 := by rw [hhead]; omega
  have hleft' : bout.tape (b.h-5) = true := by
    have heq : b.h-(3:Int)-2 = b.h-5 := by omega
    rw [heq] at hleftOut
    exact hleftOut
  have hcenter' : bout.tape (b.h-4) = true := by
    have heq : b.h-(3:Int)-1 = b.h-4 := by omega
    rw [heq] at hcenterOut
    exact hcenterOut
  have hright' : bout.tape (b.h-3) = true := by
    have heq : b.h-(3:Int) = b.h-3 := by omega
    rw [heq] at hrightOut
    exact hrightOut
  have hpres6 : ∀ x : Int, x ≤ b.h-6 →
      bout.tape x = b.tape x := by
    intro x hx
    exact hpres x (by omega)
  have hseed' : CPhaseSeed (k-1) bout := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hcases with hi0 | hi1 | hi2
      · subst i
        have hidx : bout.h-1-((0:Nat):Int) = b.h-3 := by
          rw [hhead']
          omega
        rw [hidx]
        exact hright'
      · subst i
        have hidx : bout.h-1-((1:Nat):Int) = b.h-4 := by
          rw [hhead']
          omega
        rw [hidx]
        exact hcenter'
      · subst i
        have hidx : bout.h-1-((2:Nat):Int) = b.h-5 := by
          rw [hhead']
          omega
        rw [hidx]
        exact hleft'
    · have hidx : bout.h-4 = b.h-6 := by rw [hhead']; omega
      rw [hidx]
      have hp := hpres6 (b.h-6) (by omega)
      rw [hp]
      exact hbarrier0
    · have hidx : bout.h-5 = b.h-7 := by rw [hhead']; omega
      rw [hidx]
      have hp := hpres6 (b.h-7) (by omega)
      rw [hp]
      exact hbarrier1
    · intro j hj
      have hold := hpairs (j+1) (by omega)
      have hidx1 : bout.h-7-2*(j:Int) =
          b.h-7-2*((j+1):Int) := by rw [hhead']; omega
      have hidx2 : bout.h-6-2*(j:Int) =
          b.h-6-2*((j+1):Int) := by rw [hhead']; omega
      constructor
      · rw [hidx1]
        have hp := hpres6 (b.h-7-2*((j+1):Int)) (by omega)
        rw [hp]
        exact hold.1
      · rw [hidx2]
        have hp := hpres6 (b.h-6-2*((j+1):Int)) (by omega)
        rw [hp]
        exact hold.2
  exact ⟨bout,hrun,hreach,hBzero,hhead',hseed',hnotBad⟩

/-- Repeating the C-phase return consumes an arbitrary finite alternating
    corridor.  Every checkpoint is a reached B/0, and the final checkpoint
    is outside the exact regular halting gate. -/
theorem cphase_seed_iterate (b : Conf) (k : Nat)
    (hb : Reach b) (hB : BZero b) (hseed : CPhaseSeed k b) :
    ∃ bout, shuttleRun (10*k) b = some bout ∧ Reach bout ∧ BZero bout ∧
      bout.h = b.h-2*(k:Int) ∧ ¬ BBad bout := by
  induction k generalizing b hb hB hseed with
  | zero =>
      rcases hseed with ⟨hscan,hzero,hone,_⟩
      refine ⟨b, ?_, hb, hB, ?_, ?_⟩
      · simp [shuttleRun]
      · simp
      · exact not_BBad_of_suffix10111 b hone hzero
          (hscan 2 (by omega)) (hscan 1 (by omega)) (hscan 0 (by omega))
  | succ k ih =>
      obtain ⟨b1,hrun1,hreach1,hB1,hhead1,hseed1,_⟩ :=
        cphase_seed_step b (k+1) hb hB (by omega) hseed
      obtain ⟨bout,hrun2,hreach2,hB2,hhead2,hnotBad⟩ :=
        ih b1 hreach1 hB1 hseed1
      have hrun : shuttleRun (10*(k+1)) b = some bout := by
        have htime : 10*(k+1) = 10 + 10*k := by omega
        rw [htime,shuttleRun_add,hrun1]
        simp [hrun2]
      have hhead : bout.h = b.h-2*((k+1):Int) := by
        rw [hhead2,hhead1]
        omega
      exact ⟨bout,hrun,hreach2,hB2,hhead,hnotBad⟩

/-- The odd-even prefix creates exactly n alternating pairs behind the
    C-phase D1 core.  Consequently it supports n successive ten-step
    C-phase returns, not merely the first return. -/
theorem b0_odd_even_prefix_to_cphase_seed (b : Conf) (n : Nat)
    (hb : Reach b) (hb0 : BZero b)
    (hleft : b.tape (b.h-1) = true)
    (hzero : b.tape (b.h-2) = false)
    (hone : b.tape (b.h-3) = true)
    (hones : ∀ j : Nat, j < 2*n → b.tape (b.h+1+(j:Int)) = true)
    (hterminal1 : b.tape (b.h+(2*n+1:Int)) = false)
    (hterminal2 : b.tape (b.h+(2*n+2:Int)) = false)
    (hfinal : b.tape (b.h+(2*n+3:Int)) = false) :
    ∃ b1, run (6*n+23) b = some b1 ∧ Reach b1 ∧ BZero b1 ∧
      b1.h = b.h+(2*n+3:Int) ∧ CPhaseSeed n b1 := by
  have hn : 2 ≤ n := by
    by_contra hnot
    have hcases : n = 0 ∨ n = 1 := by omega
    obtain ⟨hr1,hr2,hr3,hr4⟩ :=
      reached_B0_left10x_right1111 b hb hb0.1 hb0.2 hzero hone
    rcases hcases with hn0 | hn1
    · have hfalse : b.tape (b.h+1) = false := by
        simpa [hn0] using hterminal1
      have hfalse' : true = false := hr1.symm.trans hfalse
      cases hfalse'
    · have hfalse : b.tape (b.h+3) = false := by
        simpa [hn1] using hterminal1
      have hfalse' : true = false := hr3.symm.trans hfalse
      cases hfalse'
  obtain ⟨b1,hrun,hreach,hB,hhead,htape⟩ :=
    b0_odd_even_chain_to_b0_exact b n hb hb0 hleft hzero hone hones
      hterminal1 hterminal2 hfinal
  let tD2 : Int → Bool :=
    setBit (setBit (oddWaveTape n (twoWavePrefixTape b.tape b.h) (b.h-1))
      (b.h-2) true) (b.h-3) false
  have htape' : b1.tape =
      evenSweepBResultTape (n+1) tD2 (b.h-2) := by
    simpa [tD2] using htape
  let p : Int := (b.h-2)+2*((n+1)+1)
  have hhead' : b1.h = p+1 := by
    rw [hhead]
    dsimp [p]
    omega
  obtain ⟨hp6,hp5,hp4,hp3,hp2,hp1,hp0⟩ :=
    evenSweepBResultTape_last7 (n+1) (by omega) tD2 (b.h-2)
  have hscan : ∀ i : Nat, i < 3 →
      b1.tape (b1.h-1-(i:Int)) = true := by
    intro i hi
    have hcases : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hcases with hi0 | hi1 | hi2
    · subst i
      have hidx : b1.h-1-((0:Nat):Int) = p := by rw [hhead']; omega
      rw [htape',hidx]
      simpa [p] using hp0
    · subst i
      have hidx : b1.h-1-((1:Nat):Int) = p-1 := by rw [hhead']; omega
      rw [htape',hidx]
      simpa [p] using hp1
    · subst i
      have hidx : b1.h-1-((2:Nat):Int) = p-2 := by rw [hhead']; omega
      rw [htape',hidx]
      simpa [p] using hp2
  have hzero' : b1.tape (b1.h-4) = false := by
    have hidx : b1.h-4 = p-3 := by rw [hhead']; omega
    rw [htape',hidx]
    simpa [p] using hp3
  have hone' : b1.tape (b1.h-5) = true := by
    have hidx : b1.h-5 = p-4 := by rw [hhead']; omega
    rw [htape',hidx]
    simpa [p] using hp4
  have hkeep (x : Int) (hx0 : x ≠ p) (hx1 : x ≠ p-1) :
      evenSweepBResultTape (n+1) tD2 (b.h-2) x =
        evenSweepTape (n+2) tD2 (b.h-2) x := by
    simp [evenSweepBResultTape,p,setBit,hx0,hx1]
  have hpairs : ∀ j : Nat, j < n →
      b1.tape (b1.h-7-2*(j:Int)) = true ∧
      b1.tape (b1.h-6-2*(j:Int)) = false := by
    intro j hj
    let i : Nat := n-j-1
    have hi : i < n+2 := by dsimp [i]; omega
    have hidx1 : b1.h-7-2*(j:Int) = (b.h-2)+2*(i:Int) := by
      rw [hhead']
      dsimp [p,i]
      omega
    have hidx2 : b1.h-6-2*(j:Int) = (b.h-2)+2*(i:Int)+1 := by
      rw [hhead']
      dsimp [p,i]
      omega
    have hnot0 : (b.h-2)+2*(i:Int) ≠ p := by
      dsimp [p,i]
      omega
    have hnot1 : (b.h-2)+2*(i:Int) ≠ p-1 := by
      dsimp [p,i]
      omega
    have hnot0' : (b.h-2)+2*(i:Int)+1 ≠ p := by
      dsimp [p,i]
      omega
    have hnot1' : (b.h-2)+2*(i:Int)+1 ≠ p-1 := by
      dsimp [p,i]
      omega
    constructor
    · rw [htape',hidx1,hkeep _ hnot0 hnot1]
      exact evenSweepTape_evenCell (n+2) tD2 (b.h-2) i hi
    · rw [htape',hidx2,hkeep _ hnot0' hnot1']
      exact evenSweepTape_oddCell (n+2) tD2 (b.h-2) i hi
  exact ⟨b1,hrun,hreach,hB,hhead,hscan,hzero',hone',hpairs⟩

/-- The full odd-even macro, including every C-phase D1 return supported by
    its alternating sweep corridor, takes 16n+23 primitive steps and reaches
    a B/0 state at head h+3 outside the exact regular halting gate. -/
theorem b0_odd_even_prefix_then_cphaseD1_iterated (b : Conf) (n : Nat)
    (hb : Reach b) (hb0 : BZero b)
    (hleft : b.tape (b.h-1) = true)
    (hzero : b.tape (b.h-2) = false)
    (hone : b.tape (b.h-3) = true)
    (hones : ∀ j : Nat, j < 2*n → b.tape (b.h+1+(j:Int)) = true)
    (hterminal1 : b.tape (b.h+(2*n+1:Int)) = false)
    (hterminal2 : b.tape (b.h+(2*n+2:Int)) = false)
    (hfinal : b.tape (b.h+(2*n+3:Int)) = false) :
    ∃ bout, run (16*n+23) b = some bout ∧ Reach bout ∧ BZero bout ∧
      bout.h = b.h+3 ∧ ¬ BBad bout := by
  obtain ⟨b1,hrun1,hreach1,hB1,hhead1,hseed⟩ :=
    b0_odd_even_prefix_to_cphase_seed b n hb hb0 hleft hzero hone
      hones hterminal1 hterminal2 hfinal
  obtain ⟨bout,hrun2,hreach2,hB2,hhead2,hnotBad⟩ :=
    cphase_seed_iterate b1 n hreach1 hB1 hseed
  have hrun2' : run (10*n) b1 = some bout := by
    rw [run_eq_shuttleRun]
    exact hrun2
  have htime : 16*n+23 = (6*n+23)+(10*n) := by omega
  have hrun : run (16*n+23) b = some bout := by
    rw [htime,run_add,hrun1]
    simp [hrun2']
  have hhead : bout.h = b.h+3 := by
    rw [hhead2,hhead1]
    omega
  exact ⟨bout,hrun,hreach2,hB2,hhead,hnotBad⟩

#print axioms BB6Root119.cphase_seed_step
#print axioms BB6Root119.cphase_seed_iterate
#print axioms BB6Root119.b0_odd_even_prefix_to_cphase_seed
#print axioms BB6Root119.b0_odd_even_prefix_then_cphaseD1_iterated

end BB6Root119
