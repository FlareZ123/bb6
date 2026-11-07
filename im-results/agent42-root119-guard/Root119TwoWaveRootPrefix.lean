import Root119OddWaveRetreat

set_option linter.unusedSimpArgs false

namespace BB6Root119

/-- The nine-step B/0 prefix shared by the two-wave residual family. -/
def twoWavePrefixTape (t : Int → Bool) (h : Int) : Int → Bool :=
  setBit (setBit (setBit (setBit t h true) (h-1) true) (h-2) true) (h-3) true

theorem twoWavePrefixTape_left (t : Int → Bool) (h x : Int)
    (hx : x ≤ h-4) : twoWavePrefixTape t h x = t x := by
  have hne0 : x ≠ h := by omega
  have hne1 : x ≠ h-1 := by omega
  have hne2 : x ≠ h-2 := by omega
  have hne3 : x ≠ h-3 := by omega
  simp [twoWavePrefixTape,setBit,hne0,hne1,hne2,hne3]

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

theorem twoWaveAfterFirst_left (n : Nat) (t : Int → Bool) (h x : Int)
    (hx : x ≤ h-2) :
    (setBit (oddWaveTape n t h) (h-1) true) x = t x := by
  have hw := oddWaveTape_left n t h x (by omega)
  have hne : x ≠ h-1 := by omega
  simp [setBit,hne,hw]

/-- Exact nine-step source-machine prefix from B/0 to the first F/1 wave.
    It uses the local input pattern 1,0,1 immediately to the left of B/0. -/
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

/-- A B/0 return theorem for the two-wave residual family. The first wave
    is preceded by the exact nine-step B/0 prefix; the second wave has
    length parameter n1+2 and an arbitrary finite alternating left retreat. -/
theorem b0_two_wave_root_interval_to_b0
    (b : Conf) (n1 m : Nat)
    (hb : Reach b) (hb0 : BZero b)
    (hleft0 : b.tape (b.h-1) = true)
    (hzero0 : b.tape (b.h-2) = false)
    (hone0 : b.tape (b.h-3) = true)
    (hleft2 : b.tape (b.h-4) = true)
    (hfb : ∀ i : Nat, i < m →
      b.tape (b.h-5-2*(i:Int)) = false ∧
      b.tape (b.h-6-2*(i:Int)) = true)
    (hfinalF : b.tape (b.h-5-2*(m:Int)) = false)
    (hfinalB : b.tape (b.h-6-2*(m:Int)) = false)
    (hones1 : ∀ j : Nat, j < 2*n1 →
      b.tape (b.h+1+(j:Int)) = true)
    (hzero1 : b.tape (b.h+(2*n1+1:Int)) = false)
    (hextra : b.tape (b.h+(2*n1+2:Int)) = true)
    (hzero2 : b.tape (b.h+(2*n1+3:Int)) = false) :
    ∃ bout : Conf, Reach bout ∧ BZero bout := by
  let H : Int := b.h-1
  let t1 : Int → Bool := twoWavePrefixTape b.tape b.h
  let t2 : Int → Bool := setBit (oddWaveTape n1 t1 H) (H-1) true
  have hprefix : run 9 b = some (⟨.F,H,t1⟩ : Conf) := by
    simpa [H,t1] using b0_two_wave_prefix b hb0 hleft0 hzero0 hone0
  have hhead1 : t1 H = true := by
    dsimp [t1,H]
    simp [twoWavePrefixTape,setBit]
  have hones1' : ∀ j : Nat, j < 2*n1+1 →
      t1 (H+1+(j:Int)) = true := by
    intro j hj
    have hidx : H+1+(j:Int) = b.h+(j:Int) := by dsimp [H]; omega
    rw [hidx]
    cases j with
    | zero =>
      have hp : t1 b.h = true := by
        dsimp [t1]
        simp [twoWavePrefixTape,setBit]
      simpa using hp
    | succ k =>
      have hk : k < 2*n1 := by omega
      have hidx2 : b.h+((k+1:Nat):Int) = b.h+1+(k:Int) := by omega
      rw [hidx2]
      have hp := twoWavePrefixTape_right b.tape b.h (b.h+1+(k:Int)) (by omega)
      rw [hp]
      exact hones1 k hk
  have hzero1' : t1 (H+2*(n1:Int)+2) = false := by
    have hidx : H+2*(n1:Int)+2 = b.h+(2*n1+1:Int) := by dsimp [H]; omega
    rw [hidx]
    have hp := twoWavePrefixTape_right b.tape b.h (b.h+(2*n1+1:Int)) (by omega)
    rw [hp]
    exact hzero1
  have hleft1' : t1 (H-1) = true := by
    have hidx : H-1 = b.h-2 := by dsimp [H]; omega
    rw [hidx]
    dsimp [t1]
    simp [twoWavePrefixTape,setBit]
  have hhead2 : t2 (H-2) = true := by
    have hidx : H-2 = b.h-3 := by dsimp [H]; omega
    rw [hidx]
    have hp : t1 (b.h-3) = true := by
      dsimp [t1]
      simp [twoWavePrefixTape,setBit]
    have hw := oddWaveTape_left n1 t1 H (b.h-3) (by dsimp [H]; omega)
    have hne : b.h-3 ≠ H-1 := by dsimp [H]; omega
    dsimp [t2]
    simp [setBit,hne,hw,hp]
  have hones2 : ∀ j : Nat, j < 2*(n1+2)+1 →
      t2 (H-2+1+(j:Int)) = true := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      have hidx : H-2+1+(0:Int) = H-1 := by omega
      rw [hidx]
      dsimp [t2]
      simp [setBit]
    · by_cases hj1 : j = 1
      · subst j
        have hidx : H-2+1+(1:Int) = H := by omega
        rw [hidx]
        have hh := oddWaveTape_head n1 t1 H
        have hne : H ≠ H-1 := by omega
        dsimp [t2]
        simp [setBit,hne,hh]
      · by_cases hjLast : j = 2*n1+4
        · subst j
          have hidx : H-2+1+((2*n1+4:Nat):Int) =
              H+1+((2*n1+2:Nat):Int) := by omega
          rw [hidx]
          let x : Int := H+1+((2*n1+2:Nat):Int)
          have hout := oddWaveTape_outside_right n1 t1 H x (by dsimp [x]; omega)
          have hne : x ≠ H-1 := by dsimp [x]; omega
          have hidx2 : x = b.h+(2*n1+2:Int) := by dsimp [x,H]; omega
          have hp : t1 x = b.tape (b.h+(2*n1+2:Int)) := by
            rw [hidx2]
            exact twoWavePrefixTape_right b.tape b.h _ (by omega)
          have hval : t2 x = b.tape (b.h+(2*n1+2:Int)) := by
            dsimp [t2]
            simp [setBit,hne,hout,hp]
          rw [hval]
          exact hextra
        · have hjmid : j < 2*n1+4 := by omega
          let k : Nat := j-2
          have hk : k < 2*n1+2 := by omega
          have hidx : H-2+1+(j:Int) = H+1+(k:Int) := by dsimp [k]; omega
          rw [hidx]
          have hfill := oddWaveTape_filled n1 t1 H k hk
          have hne : H+1+(k:Int) ≠ H-1 := by omega
          dsimp [t2]
          simp [setBit,hne,hfill]
  have hzero2 : t2 (H-2+2*((n1+2):Int)+2) = false := by
    let x : Int := H-2+2*((n1+2):Int)+2
    have hidx : x = b.h+(2*n1+3:Int) := by dsimp [x,H]; omega
    have hout := oddWaveTape_outside_right n1 t1 H x (by dsimp [x]; omega)
    have hne : x ≠ H-1 := by dsimp [x]; omega
    have hp : t1 x = b.tape (b.h+(2*n1+3:Int)) := by
      rw [hidx]
      exact twoWavePrefixTape_right b.tape b.h _ (by omega)
    have hval : t2 x = b.tape (b.h+(2*n1+3:Int)) := by
      dsimp [t2]
      simp [setBit,hne,hout,hp]
    change t2 x = false
    rw [hval]
    exact hzero2
  have hleft2' : t2 (H-2-1) = true := by
    have hidx : H-2-1 = b.h-4 := by dsimp [H]; omega
    rw [hidx]
    have ha := twoWaveAfterFirst_left n1 t1 H (b.h-4) (by dsimp [H]; omega)
    rw [ha]
    have hp := twoWavePrefixTape_left b.tape b.h (b.h-4) (by omega)
    rw [hp]
    exact hleft2
  have hfb2 : ∀ i : Nat, i < m →
      t2 ((H-2)-2-2*(i:Int)) = false ∧
      t2 ((H-2)-3-2*(i:Int)) = true := by
    intro i hi
    constructor
    · have hidx : (H-2)-2-2*(i:Int) = b.h-5-2*(i:Int) := by dsimp [H]; omega
      rw [hidx]
      have ha := twoWaveAfterFirst_left n1 t1 H (b.h-5-2*(i:Int)) (by dsimp [H]; omega)
      rw [ha]
      have hp := twoWavePrefixTape_left b.tape b.h (b.h-5-2*(i:Int)) (by omega)
      rw [hp]
      exact (hfb i hi).1
    · have hidx : (H-2)-3-2*(i:Int) = b.h-6-2*(i:Int) := by dsimp [H]; omega
      rw [hidx]
      have ha := twoWaveAfterFirst_left n1 t1 H (b.h-6-2*(i:Int)) (by dsimp [H]; omega)
      rw [ha]
      have hp := twoWavePrefixTape_left b.tape b.h (b.h-6-2*(i:Int)) (by omega)
      rw [hp]
      exact (hfb i hi).2
  have hfinalF2 : t2 ((H-2)-2-2*(m:Int)) = false := by
    have hidx : (H-2)-2-2*(m:Int) = b.h-5-2*(m:Int) := by dsimp [H]; omega
    rw [hidx]
    change (setBit (oddWaveTape n1 t1 H) (H-1) true)
      (b.h-5-2*(m:Int)) = false
    have ha := twoWaveAfterFirst_left n1 t1 H (b.h-5-2*(m:Int)) (by dsimp [H]; omega)
    rw [ha]
    have hp := twoWavePrefixTape_left b.tape b.h (b.h-5-2*(m:Int)) (by omega)
    rw [hp]
    exact hfinalF
  have hfinalB2 : t2 ((H-2)-3-2*(m:Int)) = false := by
    have hidx : (H-2)-3-2*(m:Int) = b.h-6-2*(m:Int) := by dsimp [H]; omega
    rw [hidx]
    change (setBit (oddWaveTape n1 t1 H) (H-1) true)
      (b.h-6-2*(m:Int)) = false
    have ha := twoWaveAfterFirst_left n1 t1 H (b.h-6-2*(m:Int)) (by dsimp [H]; omega)
    rw [ha]
    have hp := twoWavePrefixTape_left b.tape b.h (b.h-6-2*(m:Int)) (by omega)
    rw [hp]
    exact hfinalB
  have hchain := odd_f1_two_wave_chain_to_b0 n1 (n1+2) m t1 H
    hhead1 hones1' hzero1' hleft1' hhead2 hones2 hzero2 hleft2' hfb2 hfinalF2 hfinalB2
  let out : Conf := oddRetreatResult (n1+2) m t2 (H-2)
  have htotal : 9+(4*n1+4*(n1+2)+2*m+13) =
      9+(4*n1+4*(n1+2)+2*m+13) := rfl
  have hadd := run_add 9 (4*n1+4*(n1+2)+2*m+13) b
  have hrun : run (9+(4*n1+4*(n1+2)+2*m+13)) b = some out := by
    rw [hadd,hprefix]
    simp only [Option.bind_some]
    simpa [out,t2] using hchain.1
  have houtReach : Reach out :=
    reachable_of_run (9+(4*n1+4*(n1+2)+2*m+13)) b out hb hrun
  have houtB : BZero out := by
    refine ⟨rfl,?_⟩
    simpa [out,oddRetreatResult,t2] using hchain.2
  exact ⟨out,houtReach,houtB⟩

#print axioms BB6Root119.b0_two_wave_prefix
#print axioms BB6Root119.b0_two_wave_root_interval_to_b0

end BB6Root119
