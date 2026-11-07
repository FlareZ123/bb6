import Root119OddWaveRetreat
import Root119ParityDichotomy

set_option linter.unusedSimpArgs false

namespace BB6Root119


/-- The exact nine-step B/0 prefix writes four consecutive ones and reaches
    F/1 one cell to the left. -/
def twoWavePrefixTape (t : Int → Bool) (h : Int) : Int → Bool :=
  setBit (setBit (setBit (setBit t h true) (h-1) true) (h-2) true) (h-3) true

theorem twoWavePrefixTape_right (t : Int → Bool) (h x : Int)
    (hx : h < x) : twoWavePrefixTape t h x = t x := by
  have hne0 : x ≠ h := by omega
  have hne1 : x ≠ h-1 := by omega
  have hne2 : x ≠ h-2 := by omega
  have hne3 : x ≠ h-3 := by omega
  simp [twoWavePrefixTape,setBit,hne0,hne1,hne2,hne3]

theorem oddWaveTape_head (n : Nat) (t : Int → Bool) (h : Int) :
    oddWaveTape n t h h = true := by
  simp [oddWaveTape,setBit]

theorem oddWaveTape_filled (n : Nat) (t : Int → Bool) (h : Int) (k : Nat)
    (hk : k < 2*n+2) :
    oddWaveTape n t h (h+1+(k:Int)) = true := by
  have hne : h+1+(k:Int) ≠ h := by omega
  have hinside : h+1 ≤ h+1+(k:Int) ∧
      h+1+(k:Int) < h+1+(2*n+2:Int) := by omega
  simp [oddWaveTape,shuttleFill,setBit,hne,hinside]

theorem oddWaveTape_outside_right (n : Nat) (t : Int → Bool) (h x : Int)
    (hx : h+1+(2*n+2:Int) ≤ x) :
    oddWaveTape n t h x = t x := by
  have hout := shuttleFill_outside (setBit t h false) (h+1) x (2*n+2)
    (Or.inr (by omega))
  have hne : x ≠ h := by omega
  simp [oddWaveTape,setBit,hne,hout]

theorem b0_two_wave_prefix (b : Conf) (hb0 : BZero b)
    (hleft : b.tape (b.h-1) = true)
    (hzero : b.tape (b.h-2) = false)
    (hone : b.tape (b.h-3) = true) :
    run 9 b = some (⟨.F,b.h-1,twoWavePrefixTape b.tape b.h⟩ : Conf) := by
  rcases b with ⟨q,h,t⟩
  obtain ⟨hq,hb⟩ := hb0
  change q = .B at hq
  subst q
  change t h = false at hb
  change t (h-1) = true at hleft
  change t (h-2) = false at hzero
  change t (h-3) = true at hone
  let t1 := setBit t h true
  let t2 := setBit t1 (h-1) false
  let t3 := setBit t2 (h-2) true
  let t4 := setBit t3 (h-3) true
  let t5 := setBit t4 (h-2) false
  let t6 := setBit t5 (h-1) false
  let t7 := setBit t6 (h-2) true
  let t8 := setBit t7 (h-1) true
  let t9 := setBit t8 h true
  let c0 : Conf := ⟨.B,h,t⟩
  let c1 : Conf := ⟨.C,h-1,t1⟩
  let c2 : Conf := ⟨.C,h-2,t2⟩
  let c3 : Conf := ⟨.D,h-3,t3⟩
  let c4 : Conf := ⟨.F,h-2,t4⟩
  let c5 : Conf := ⟨.D,h-1,t5⟩
  let c6 : Conf := ⟨.E,h-2,t6⟩
  let c7 : Conf := ⟨.A,h-1,t7⟩
  let c8 : Conf := ⟨.B,h,t8⟩
  let c9 : Conf := ⟨.F,h-1,t9⟩
  have h01 : next c0 = some c1 := by simp [next,c0,c1,t1,hb]
  have h12 : next c1 = some c2 := by
    have hr : t1 (h-1) = true := by
      simp [t1,setBit,show h-1 ≠ h by omega,hleft]
    have hp : h-1-1 = h-2 := by omega
    simp [next,c1,c2,t1,t2,hr,hp]
  have h23 : next c2 = some c3 := by
    have hr : t2 (h-2) = false := by
      simp [t2,t1,setBit,show h-2 ≠ h-1 by omega,
        show h-2 ≠ h by omega,hzero]
    have hp : h-2-1 = h-3 := by omega
    simp [next,c2,c3,t2,t1,t3,setBit,hr,hp]
  have h34 : next c3 = some c4 := by
    have hr : t3 (h-3) = true := by
      simp [t3,t2,t1,setBit,show h-3 ≠ h-2 by omega,
        show h-3 ≠ h-1 by omega,show h-3 ≠ h by omega,hone]
    have hp : h-3+1 = h-2 := by omega
    simp [next,c3,c4,t3,t4,hr,hp]
  have h45 : next c4 = some c5 := by
    have hr : t4 (h-2) = true := by
      simp [t4,t3,t2,t1,setBit,show h-2 ≠ h-3 by omega,
        show h-2 ≠ h by omega]
    have hp : h-2+1 = h-1 := by omega
    simp [next,c4,c5,t4,t5,hr,hp]
  have h56 : next c5 = some c6 := by
    have hr : t5 (h-1) = false := by
      simp [t5,t4,t3,t2,t1,setBit,show h-1 ≠ h-2 by omega,
        show h-1 ≠ h by omega]
    have hp : h-1-1 = h-2 := by omega
    simp [next,c5,c6,t5,t6,hr,hp]
  have h67 : next c6 = some c7 := by
    have hr : t6 (h-2) = false := by
      simp [t6,t5,t4,t3,t2,t1,setBit,show h-2 ≠ h-1 by omega,
        show h-2 ≠ h-3 by omega,show h-2 ≠ h by omega]
    have hp : h-2+1 = h-1 := by omega
    simp [next,c6,c7,t6,t7,hr,hp]
  have h78 : next c7 = some c8 := by
    have hr : t7 (h-1) = false := by
      simp [t7,t6,t5,t4,t3,t2,t1,setBit,show h-1 ≠ h-2 by omega,
        show h-1 ≠ h by omega]
    have hp : h-1+1 = h := by omega
    simp [next,c7,c8,t7,t8,hr,hp]
  have hne1 : h ≠ h-1 := by omega
  have hne2 : h ≠ h-2 := by omega
  have hne3 : h ≠ h-3 := by omega
  have hr : t8 h = true := by
    simp [t8,t7,t6,t5,t4,t3,t2,t1,setBit,hne1,hne2,hne3]
  have h89 : next c8 = some c9 := by
    simp [next,c8,c9,t8,t9,hr]
  have hrun : run 9 c0 = some c9 := by
    simp [run,h01,h12,h23,h34,h45,h56,h67,h78,h89]
  have htape : t9 = twoWavePrefixTape t h := by
    funext x
    simp only [t9,t8,t7,t6,t5,t4,t3,t2,t1,twoWavePrefixTape,setBit]
    by_cases hx0 : x = h
    · simp [hx0]
    · by_cases hx1 : x = h-1
      · simp [hx0,hx1]
      · by_cases hx2 : x = h-2
        · simp [hx0,hx1,hx2]
        · by_cases hx3 : x = h-3
          · simp [hx0,hx1,hx2,hx3]
          · simp [hx0,hx1,hx2,hx3]
  simpa [c0,c9,htape] using hrun

/-- The exact tape after an even D/1-F/1 sweep and its D/0-E/0-A/0 finish. -/
def evenSweepBResultTape (n : Nat) (t : Int → Bool) (h : Int) : Int → Bool :=
  let p : Int := h + 2*(n+1)
  setBit (setBit (setBit (evenSweepTape (n+1) t h) p false) (p-1) true) p true

theorem evenSweepBResultTape_farRight (n : Nat) (t : Int → Bool) (h x : Int)
    (hx : h+2*(n+1) < x) :
    evenSweepBResultTape n t h x = t x := by
  simp [evenSweepBResultTape, setBit,
    show x ≠ h+2*(n+1) by omega,
    show x ≠ h+2*(n+1)-1 by omega]
  exact evenSweepTape_right (n+1) t h x (by omega)

/-- The final B cell of an even sweep is outside every write of the macro. -/
theorem evenSweepBResultTape_finalCell (n : Nat) (t : Int → Bool) (h : Int) :
    evenSweepBResultTape n t h (h+2*(n+1)+1) =
      t (h+2*(n+1)+1) := by
  exact evenSweepBResultTape_farRight n t h _ (by omega)

/-- Exact full-configuration form of Agent 12's positive even-run D sweep. -/
theorem evenSweep_to_B_exact (n : Nat) (t : Int → Bool) (h : Int)
    (ones : ∀ j : Nat, j < 2*(n+1) → t (h+(j:Int)) = true)
    (zero : t (h+(2*(n+1):Int)) = false) :
    run (2*(n+1)+3) (⟨.D,h,t⟩ : Conf) =
      some ⟨.B,h+2*(n+1)+1,evenSweepBResultTape n t h⟩ := by
  rw [run_eq_shuttleRun]
  let p : Int := h+2*(n+1)
  let v : Int → Bool := evenSweepTape (n+1) t h
  have ds : shuttleRun (2*(n+1)) (⟨.D,h,t⟩ : Conf) =
      some ⟨.D,p,v⟩ := by
    simpa [p,v] using evenSweep (n+1) t h ones
  have hz : v p = false := by
    have hh := evenSweepTape_right (n+1) t h p (by dsimp [p]; omega)
    dsimp [p,v] at hh ⊢
    exact hh.trans zero
  have hl : v (p-1) = false := by
    dsimp [p,v]
    exact evenSweepTape_last n t h
  let v1 := setBit v p false
  let v2 := setBit v1 (p-1) true
  let v3 := setBit v2 p true
  have hleft : v1 (p-1) = false := by
    have hne : p-1 ≠ p := by omega
    simp [v1,setBit,hne,hl]
  have hright : v2 p = false := by
    have hne : p ≠ p-1 := by omega
    simp [v2,setBit,hne,v1,hz]
  have hs1 : next ⟨.D,p,v⟩ = some ⟨.E,p-1,v1⟩ := by
    simp [next,hz,v1]
  have hs2 : next ⟨.E,p-1,v1⟩ = some ⟨.A,p,v2⟩ := by
    simp [next,hleft,v2]
  have hs3 : next ⟨.A,p,v2⟩ = some ⟨.B,p+1,v3⟩ := by
    simp [next,hright,v3]
  have ht : shuttleRun 3 ⟨.D,p,v⟩ = some ⟨.B,p+1,v3⟩ := by
    simp [shuttleRun,hs1,hs2,hs3]
  have hrun : shuttleRun (2*(n+1)+3) (⟨.D,h,t⟩ : Conf) =
      some ⟨.B,p+1,v3⟩ := by
    calc
      shuttleRun (2*(n+1)+3) (⟨.D,h,t⟩ : Conf) =
          (shuttleRun (2*(n+1)) (⟨.D,h,t⟩ : Conf)).bind (shuttleRun 3) := by
            rw [shuttleRun_add]
      _ = (some ⟨.D,p,v⟩).bind (shuttleRun 3) := by rw [ds]
      _ = some ⟨.B,p+1,v3⟩ := by simp [ht]
  simpa [p,evenSweepBResultTape,v,v1,v2,v3] using hrun

/-- A nine-step B/0 prefix followed by an even F/1 sweep returns to B/0.
    The run-length and two terminal-zero hypotheses are the complete tape
    conditions; all exterior tape is arbitrary. -/
theorem b0_even_prefix_to_b0 (b : Conf) (n : Nat)
    (hb : Reach b) (hb0 : BZero b)
    (hleft : b.tape (b.h-1) = true)
    (hzero : b.tape (b.h-2) = false)
    (hone : b.tape (b.h-3) = true)
    (hones : ∀ j : Nat, j < 2*n+1 →
      b.tape (b.h+1+(j:Int)) = true)
    (hterminal : b.tape (b.h+(2*(n+1):Int)) = false)
    (hfinal : b.tape (b.h+(2*(n+1):Int)+1) = false) :
    ∃ bout : Conf, run (2*n+15) b = some bout ∧
      Reach bout ∧ BZero bout := by
  let f : Conf := ⟨.F,b.h-1,twoWavePrefixTape b.tape b.h⟩
  let tD : Int → Bool :=
    setBit (twoWavePrefixTape b.tape b.h) (b.h-1) false
  let d : Conf := ⟨.D,b.h,tD⟩
  let bout : Conf := ⟨.B,b.h+2*(n+1)+1,evenSweepBResultTape n tD b.h⟩
  have hprefix : run 9 b = some f := by
    simpa [f] using b0_two_wave_prefix b hb0 hleft hzero hone
  have hfhead : twoWavePrefixTape b.tape b.h (b.h-1) = true := by
    simp [twoWavePrefixTape,setBit]
  have hfstep : run 1 f = some d := by
    have hs : next f = some d := by
      simp [next,f,d,tD,hfhead]
    simp [run,hs]
  have honesD : ∀ j : Nat, j < 2*(n+1) → tD (b.h+(j:Int)) = true := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp [tD,twoWavePrefixTape,setBit]
    · have hjpos : 1 ≤ j := by omega
      have hne : b.h+(j:Int) ≠ b.h-1 := by omega
      calc
        tD (b.h+(j:Int)) =
            twoWavePrefixTape b.tape b.h (b.h+(j:Int)) := by
              simp [tD,setBit,hne]
        _ = b.tape (b.h+(j:Int)) :=
          twoWavePrefixTape_right b.tape b.h (b.h+(j:Int)) (by omega)
        _ = b.tape (b.h+1+((j-1:Nat):Int)) := by congr 1 <;> omega
        _ = true := hones (j-1) (by omega)
  have hzeroD : tD (b.h+(2*(n+1):Int)) = false := by
    have hne : b.h+(2*(n+1):Int) ≠ b.h-1 := by omega
    calc
      tD (b.h+(2*(n+1):Int)) =
          twoWavePrefixTape b.tape b.h (b.h+(2*(n+1):Int)) := by
            simp [tD,setBit,hne]
      _ = b.tape (b.h+(2*(n+1):Int)) :=
        twoWavePrefixTape_right b.tape b.h _ (by omega)
      _ = false := hterminal
  have hEven := evenSweep_to_B_exact n tD b.h honesD hzeroD
  have hfinalTape :
      evenSweepBResultTape n tD b.h (b.h+2*(n+1)+1) = false := by
    rw [evenSweepBResultTape_finalCell]
    have hne : b.h+2*(n+1)+1 ≠ b.h-1 := by omega
    calc
      tD (b.h+2*(n+1)+1) =
          twoWavePrefixTape b.tape b.h (b.h+2*(n+1)+1) := by
            simp [tD,setBit,hne]
      _ = b.tape (b.h+2*(n+1)+1) :=
        twoWavePrefixTape_right b.tape b.h _ (by omega)
      _ = false := hfinal
  have hboutZero : BZero bout := by
    refine ⟨rfl,?_⟩
    simpa [bout] using hfinalTape
  have hrunD : run (2*(n+1)+3) d = some bout := by
    simpa [d,bout,tD] using hEven
  have htime : 2*n+15 = 9 + (1+(2*(n+1)+3)) := by omega
  have hrun : run (2*n+15) b = some bout := by
    rw [htime]
    calc
      run (9+(1+(2*(n+1)+3))) b =
          (run 9 b).bind (run (1+(2*(n+1)+3))) := by rw [run_add]
      _ = run (1+(2*(n+1)+3)) f := by simp [hprefix]
      _ = (run 1 f).bind (run (2*(n+1)+3)) := by rw [run_add]
      _ = run (2*(n+1)+3) d := by simp [hfstep]
      _ = some bout := hrunD
  exact ⟨bout,hrun,reachable_of_run (2*n+15) b bout hb hrun,hboutZero⟩

/-- An odd F/1 sweep followed by the B/1-F/1 transition and an even sweep
    also returns to B/0.  This is the second residual prefix family. -/
theorem b0_odd_even_chain_to_b0 (b : Conf) (n : Nat)
    (hb : Reach b) (hb0 : BZero b)
    (hleft : b.tape (b.h-1) = true)
    (hzero : b.tape (b.h-2) = false)
    (hone : b.tape (b.h-3) = true)
    (hones : ∀ j : Nat, j < 2*n →
      b.tape (b.h+1+(j:Int)) = true)
    (hterminal1 : b.tape (b.h+(2*n+1:Int)) = false)
    (hterminal2 : b.tape (b.h+(2*n+2:Int)) = false)
    (hfinal : b.tape (b.h+(2*n+3:Int)) = false) :
    ∃ bout : Conf, run (6*n+23) b = some bout ∧
      Reach bout ∧ BZero bout := by
  let H : Int := b.h-1
  let t1 : Int → Bool := twoWavePrefixTape b.tape b.h
  let f1 : Conf := ⟨.F,H,t1⟩
  let b1Tape : Int → Bool := oddWaveTape n t1 H
  let b1 : Conf := ⟨.B,H-1,b1Tape⟩
  let f2Tape : Int → Bool := setBit b1Tape (H-1) true
  let f2 : Conf := ⟨.F,H-2,f2Tape⟩
  let tD2 : Int → Bool := setBit f2Tape (H-2) false
  let d2 : Conf := ⟨.D,H-1,tD2⟩
  let bout : Conf :=
    ⟨.B,H-1+2*((n+1)+1)+1,evenSweepBResultTape (n+1) tD2 (H-1)⟩
  have hprefix : run 9 b = some f1 := by
    simpa [f1,H,t1] using b0_two_wave_prefix b hb0 hleft hzero hone
  have hfhead : t1 H = true := by
    simp [t1,H,twoWavePrefixTape,setBit]
  have hones1 : ∀ j : Nat, j < 2*n+1 →
      t1 (H+1+(j:Int)) = true := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      have hh : H+1 = b.h := by dsimp [H]; omega
      rw [hh]
      simp [t1,twoWavePrefixTape,setBit]
    · have hjpos : 1 ≤ j := by omega
      have hidx : H+1+(j:Int) = b.h+1+((j-1:Nat):Int) := by
        dsimp [H]
        omega
      rw [hidx]
      have hright := twoWavePrefixTape_right b.tape b.h
        (b.h+1+((j-1:Nat):Int)) (by omega)
      rw [t1,hright]
      exact hones (j-1) (by omega)
  have hzero1 : t1 (H+2*(n:Int)+2) = false := by
    have hidx : H+2*(n:Int)+2 = b.h+(2*n+1:Int) := by
      dsimp [H]
      omega
    rw [hidx]
    rw [twoWavePrefixTape_right b.tape b.h _ (by omega)]
    exact hterminal1
  have hWave : run (4*n+5) f1 = some b1 := by
    simpa [b1,b1Tape] using odd_f1_to_b n t1 H hfhead hones1 hzero1
  have hb1bit : b1Tape (H-1) = true := by
    change oddWaveTape n t1 H (H-1) = true
    rw [oddWaveTape_left n t1 H (H-1) (by omega)]
    have hbit : t1 (H-1) = true := by
      simp [t1,H,twoWavePrefixTape,setBit]
    exact hbit
  have hBstep : run 1 b1 = some f2 := by
    have hs : next b1 = some f2 := by
      simp [next,b1,f2,b1Tape,f2Tape,hb1bit]
    simp [run,hs]
  have hf2bit : f2Tape (H-2) = true := by
    have hne : H-2 ≠ H-1 := by omega
    simp [f2Tape,setBit,hne]
    change oddWaveTape n t1 H (H-2) = true
    rw [oddWaveTape_left n t1 H (H-2) (by omega)]
    have hbit : t1 (H-2) = true := by
      simp [t1,H,twoWavePrefixTape,setBit]
    exact hbit
  have hF2step : run 1 f2 = some d2 := by
    have hs : next f2 = some d2 := by
      simp [next,f2,d2,tD2,hf2bit]
    simp [run,hs]
  have honesD2 : ∀ j : Nat, j < 2*(n+2) →
      tD2 (H-1+(j:Int)) = true := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp [tD2,f2Tape,f2,b1Tape,b1,f2Tape,setBit]
    · by_cases hj1 : j = 1
      · subst j
        have hh : H-1+((1:Nat):Int) = H := by omega
        rw [hh]
        have hhead : b1Tape H = true := by
          simpa [b1Tape] using oddWaveTape_head n t1 H
        have hne1 : H ≠ H-1 := by omega
        have hne2 : H ≠ H-2 := by omega
        simp [tD2,f2Tape,setBit,hne1,hne2,hhead]
      · have hjpos : 2 ≤ j := by omega
        have hidx : H-1+(j:Int) = H+1+((j-2:Nat):Int) := by omega
        rw [hidx]
        have hfill := oddWaveTape_filled n t1 H (j-2) (by omega)
        simp [tD2,f2Tape,b1Tape,setBit,show H+1+((j-2:Nat):Int) ≠ H-1 by omega,
          show H+1+((j-2:Nat):Int) ≠ H-2 by omega,hfill]
  have hzeroD2 :
      tD2 (H-1+(2*(n+2):Int)) = false := by
    have hidx : H-1+(2*(n+2):Int) = H+2*(n:Int)+3 := by omega
    rw [hidx]
    have hidx2 : H+2*(n:Int)+3 = b.h+(2*n+2:Int) := by
      dsimp [H]
      omega
    calc
      tD2 (H+2*(n:Int)+3) = b1Tape (H+2*(n:Int)+3) := by
        simp [tD2,f2Tape,setBit,
          show H+2*(n:Int)+3 ≠ H-1 by omega,
          show H+2*(n:Int)+3 ≠ H-2 by omega]
      _ = t1 (H+2*(n:Int)+3) :=
        oddWaveTape_outside_right n t1 H (H+2*(n:Int)+3) (by omega)
      _ = b.tape (H+2*(n:Int)+3) :=
        twoWavePrefixTape_right b.tape b.h _ (by omega)
      _ = false := by rw [hidx2]; exact hterminal2
  have hEven := evenSweep_to_B_exact (n+1) tD2 (H-1) honesD2 hzeroD2
  have hfinalTape :
      evenSweepBResultTape (n+1) tD2 (H-1)
        (H-1+2*((n+1)+1)+1) = false := by
    have hcell := evenSweepBResultTape_finalCell (n+1) tD2 (H-1)
    have hcell' :
        evenSweepBResultTape (n+1) tD2 (H-1)
          (H-1+2*((n+1)+1)+1) =
          tD2 (H-1+2*((n+1)+1)+1) := by
      simpa only [Nat.cast_add] using hcell
    have hidx2 : H-1+2*((n+1)+1)+1 = b.h+(2*n+3:Int) := by
      dsimp [H]
      omega
    calc
      evenSweepBResultTape (n+1) tD2 (H-1)
          (H-1+2*((n+1)+1)+1) =
          tD2 (H-1+2*((n+1)+1)+1) := hcell'
      _ = b1Tape (H-1+2*((n+1)+1)+1) := by
        simp [tD2,f2Tape,b1Tape,setBit,
          show H-1+2*((n+1)+1)+1 ≠ H-1 by omega,
          show H-1+2*((n+1)+1)+1 ≠ H-2 by omega]
      _ = t1 (H-1+2*((n+1)+1)+1) :=
        oddWaveTape_outside_right n t1 H _ (by omega)
      _ = b.tape (H-1+2*((n+1)+1)+1) :=
        twoWavePrefixTape_right b.tape b.h _ (by omega)
      _ = false := by rw [hidx2]; exact hfinal
  have hboutZero : BZero bout := by
    refine ⟨rfl,?_⟩
    simpa [bout] using hfinalTape
  have hrunD2 : run (2*((n+1)+1)+3) d2 = some bout := by
    simpa [d2,bout,tD2] using hEven
  have htime : 6*n+23 =
      9 + ((4*n+5) + (1+(1+(2*((n+1)+1)+3)))) := by omega
  have hrun : run (6*n+23) b = some bout := by
    rw [htime]
    calc
      run (9+((4*n+5)+(1+(1+(2*((n+1)+1)+3))))) b =
          (run 9 b).bind
            (run ((4*n+5)+(1+(1+(2*((n+1)+1)+3)))) ) := by rw [run_add]
      _ = run ((4*n+5)+(1+(1+(2*((n+1)+1)+3)))) f1 := by simp [hprefix]
      _ = (run (4*n+5) f1).bind
            (run (1+(1+(2*((n+1)+1)+3)))) := by rw [run_add]
      _ = run (1+(1+(2*((n+1)+1)+3))) b1 := by simp [hWave]
      _ = (run 1 b1).bind (run (1+(2*((n+1)+1)+3))) := by rw [run_add]
      _ = run (1+(2*((n+1)+1)+3)) f2 := by simp [hBstep]
      _ = (run 1 f2).bind (run (2*((n+1)+1)+3)) := by rw [run_add]
      _ = run (2*((n+1)+1)+3) d2 := by simp [hF2step]
      _ = some bout := hrunD2
  exact ⟨bout,hrun,reachable_of_run (6*n+23) b bout hb hrun,hboutZero⟩

#print axioms BB6Root119.evenSweep_to_B_exact
#print axioms BB6Root119.twoWavePrefixTape
#print axioms BB6Root119.twoWavePrefixTape_right
#print axioms BB6Root119.b0_two_wave_prefix
#print axioms BB6Root119.reachable_of_run
#print axioms BB6Root119.run_add
#print axioms BB6Root119.evenSweepBResultTape_finalCell
#print axioms BB6Root119.odd_f1_to_b
#print axioms BB6Root119.b0_even_prefix_to_b0
#print axioms BB6Root119.b0_odd_even_chain_to_b0

end BB6Root119
