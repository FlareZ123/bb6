import Root119BRegular
import Root119BShield
import Root119ShuttleSupport
set_option linter.unusedSimpArgs false
namespace BB6Root119

theorem noLeft4_excludes_BBad (b : Conf)
    (hs : NoLeft4 true true false b) : ¬BBad b := by
  rintro ⟨_,r,_,h0,h1,h2,h3⟩
  have hbound : b.h-4-(r:Int)+3 < b.h := by omega
  have hidx1 : b.h-4-(r:Int)+1 = b.h-3-(r:Int) := by omega
  have hidx2 : b.h-4-(r:Int)+2 = b.h-2-(r:Int) := by omega
  have hidx3 : b.h-4-(r:Int)+3 = b.h-1-(r:Int) := by omega
  apply hs (b.h-4-(r:Int)) hbound
  refine ⟨h3,?_,?_,?_⟩
  · rw [hidx1]; exact h2
  · rw [hidx2]; exact h1
  · rw [hidx3]; exact h0

/-- The B-to-C scan has exact duration r+1 and erases every scanned one. -/
theorem scan_from_B_exact (b : Conf) (hb : Reach b) (hB : BZero b)
    (r : Nat)
    (hones : ∀ i : Nat, i < r → b.tape (b.h-1-(i:Int)) = true) :
    ∃ c, shuttleRun (r+1) b = some c ∧ Reach c ∧ CPhase b c r ∧
      (∀ i : Nat, i < r → c.tape (b.h-1-(i:Int)) = false) := by
  induction r with
  | zero =>
      obtain ⟨c,hstep⟩ := B_always_moves b hB.1
      have hrun : shuttleRun (0+1) b = some c := by
        simp [shuttleRun,hstep]
      exact ⟨c,hrun,Reach.follow hb hstep,CPhase_from_B hB hstep,by omega⟩
  | succ r ih =>
      have hpre : ∀ i : Nat, i < r → b.tape (b.h-1-(i:Int)) = true := by
        intro i hi
        exact hones i (by omega)
      obtain ⟨c,hrun,hc,hphase,hzeros⟩ := ih hpre
      have hC : c.q = .C := hphase.2.1
      have hpos : c.h = b.h-1-(r:Int) := hphase.2.2.1
      have hprefix : ∀ x : Int, x ≤ c.h → c.tape x = b.tape x := hphase.2.2.2.1
      have hbit : c.tape c.h = true := by
        calc
          c.tape c.h = b.tape c.h := hprefix c.h (by omega)
          _ = b.tape (b.h-1-(r:Int)) := by rw [hpos]
          _ = true := hones r (by omega)
      let d : Conf := ⟨.C,c.h-1,setBit c.tape c.h false⟩
      have hstep : next c = some d := by
        rcases c with ⟨q,pos,t⟩
        change q = .C at hC
        subst q
        change t pos = true at hbit
        simp [next,d,hbit]
      have hphase' : CPhase b d (r+1) := CPhase_follow_C hphase hbit hstep
      have hzeros' : ∀ i : Nat, i < r+1 → d.tape (b.h-1-(i:Int)) = false := by
        intro i hi
        by_cases hlt : i < r
        · have hne : b.h-1-(i:Int) ≠ c.h := by rw [hpos]; omega
          have hne' : b.h-(1+(i:Int)) ≠ c.h := by omega
          change setBit c.tape c.h false (b.h-1-(i:Int)) = false
          simp [setBit,hne,hne',hzeros i hlt]
        · have heq : i = r := by omega
          subst i
          have hidx : b.h-1-(r:Int) = c.h := by omega
          rw [hidx]
          change setBit c.tape c.h false c.h = false
          simp [setBit]
      have htime : r+1+1 = (r+1)+1 := by omega
      have hrun' : shuttleRun (r+1+1) b = some d := by
        rw [shuttleRun_add (r+1) 1 b,hrun]
        simp [shuttleRun,hstep]
      exact ⟨d,by simpa [htime] using hrun',Reach.follow hc hstep,hphase',hzeros'⟩

/-- The six-step C/0-D/1-F/1-D/0-E/0-A/0 tail returns to B/0. -/
theorem cphase_d1_tail (c : Conf) (hc : Reach c)
    (hC : c.q = .C) (hCzero : c.tape c.h = false)
    (hDone : c.tape (c.h-1) = true)
    (hzero1 : c.tape (c.h+1) = false)
    (hzero2 : c.tape (c.h+2) = false)
    (hshield : NoLeft4 true true false c) :
    ∃ bout, shuttleRun 6 c = some bout ∧ Reach bout ∧ BZero bout ∧
      bout.h = c.h+2 ∧ NoLeft4 true true false bout := by
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
  have hshield' : NoLeft4 true true false bout := by
    intro x hx hw
    change x+3 < c.h+2 at hx
    have hcase : x+3 ≤ c.h-2 ∨ x+3 = c.h-1 ∨
        x+3 = c.h ∨ x+3 = c.h+1 := by omega
    rcases hcase with hfar | h1 | h2 | h3
    · have hw' : c.tape x = true ∧ c.tape (x+1) = true ∧
          c.tape (x+2) = false ∧ c.tape (x+3) = false := by
        rcases hw with ⟨h0,h1',h2',h3'⟩
        exact ⟨by rw [← htail_left x (by omega)]; exact h0,
          by rw [← htail_left (x+1) (by omega)]; exact h1',
          by rw [← htail_left (x+2) (by omega)]; exact h2',
          by rw [← htail_left (x+3) (by omega)]; exact h3'⟩
      exact hshield x (by omega) hw'
    · have hlast : bout.tape (x+3) = true := by rw [h1]; exact hleftFinal
      have hfalse : bout.tape (x+3) = false := hw.2.2.2
      rw [hlast] at hfalse
      contradiction
    · have hlast : bout.tape (x+3) = true := by rw [h2]; exact hcenterFinal
      have hfalse : bout.tape (x+3) = false := hw.2.2.2
      rw [hlast] at hfalse
      contradiction
    · have hlast : bout.tape (x+3) = true := by rw [h3]; exact hrightFinal
      have hfalse : bout.tape (x+3) = false := hw.2.2.2
      rw [hlast] at hfalse
      contradiction
  exact ⟨bout,hrun,hreach,hBzero,rfl,hshield'⟩

/-- A B/0 with r≥2 leftward ones, then 0,1, returns in exactly r+7 steps. -/
theorem b0_cphase_d1_zero_wave_return (b : Conf) (r : Nat)
    (hb : Reach b) (hB : BZero b) (hr : 2 ≤ r)
    (hscan : ∀ i : Nat, i < r → b.tape (b.h-1-(i:Int)) = true)
    (hzeroC : b.tape (b.h-1-(r:Int)) = false)
    (honeD : b.tape (b.h-2-(r:Int)) = true)
    (hshield : NoLeft4 true true false b) :
    ∃ bout, shuttleRun (r+7) b = some bout ∧ Reach bout ∧ BZero bout ∧
      bout.h = b.h-(r:Int)+1 ∧ NoLeft4 true true false bout ∧ ¬BBad bout := by
  obtain ⟨c,hscanRun,hc,hphase,hzeros⟩ := scan_from_B_exact b hb hB r hscan
  have hpos : c.h = b.h-1-(r:Int) := hphase.2.2.1
  have hprefix : ∀ x : Int, x ≤ c.h → c.tape x = b.tape x := hphase.2.2.2.1
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
  have hcshield : NoLeft4 true true false c := by
    intro x hx hw
    have hxB : x+3 < b.h := by rw [hpos] at hx; omega
    have hwB : b.tape x = true ∧ b.tape (x+1) = true ∧
        b.tape (x+2) = false ∧ b.tape (x+3) = false := by
      rcases hw with ⟨h0,h1,h2,h3⟩
      exact ⟨by rw [← hprefix x (by omega)]; exact h0,
        by rw [← hprefix (x+1) (by omega)]; exact h1,
        by rw [← hprefix (x+2) (by omega)]; exact h2,
        by rw [← hprefix (x+3) (by omega)]; exact h3⟩
    exact hshield x hxB hwB
  obtain ⟨bout,htail,hbout,hBzero,hheadTail,hboutShield⟩ :=
    cphase_d1_tail c hc hC hCzero hDone hzero1 hzero2 hcshield
  have htime : r+7 = (r+1)+6 := by omega
  have hrun : shuttleRun (r+7) b = some bout := by
    rw [htime,shuttleRun_add,hscanRun]
    simp [htail]
  have hhead : bout.h = b.h-(r:Int)+1 := by
    rw [hheadTail,hpos]
    omega
  exact ⟨bout,hrun,hbout,hBzero,hhead,hboutShield,
    noLeft4_excludes_BBad bout hboutShield⟩

#print axioms BB6Root119.noLeft4_excludes_BBad
#print axioms BB6Root119.scan_from_B_exact
#print axioms BB6Root119.cphase_d1_tail
#print axioms BB6Root119.b0_cphase_d1_zero_wave_return
end BB6Root119
