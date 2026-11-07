import Root119OddWaveRetreat
import Root119FBSweep

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

theorem noLeft4_transfer_of_left_agreement (p q r : Bool) (c d : Conf)
    (hhead : d.h ≤ c.h)
    (hagree : ∀ x : Int, x < d.h → d.tape x = c.tape x)
    (hc : NoLeft4 p q r c) : NoLeft4 p q r d := by
  intro x hx hword
  change x+3 < d.h at hx
  have hxOld : x+3 < c.h := by omega
  apply hc x hxOld
  refine ⟨?_,?_,?_,?_⟩
  · calc
      c.tape x = d.tape x := (hagree x (by omega)).symm
      _ = p := hword.1
  · calc
      c.tape (x+1) = d.tape (x+1) := (hagree (x+1) (by omega)).symm
      _ = q := hword.2.1
  · calc
      c.tape (x+2) = d.tape (x+2) := (hagree (x+2) (by omega)).symm
      _ = r := hword.2.2.1
  · calc
      c.tape (x+3) = d.tape (x+3) := (hagree (x+3) (by omega)).symm
      _ = false := hword.2.2.2

theorem noLeft4_left_write (p q r : Bool) (c : Conf)
    (hc : NoLeft4 p q r c) :
    NoLeft4 p q r ⟨.B,c.h-1,setBit c.tape c.h true⟩ := by
  intro x hx hword
  change x+3 < c.h-1 at hx
  have hxOld : x+3 < c.h := by omega
  apply hc x hxOld
  refine ⟨?_,?_,?_,?_⟩
  · have hunchanged : setBit c.tape c.h true x = c.tape x := by
      simp [setBit,show x ≠ c.h by omega]
    calc
      c.tape x = setBit c.tape c.h true x := hunchanged.symm
      _ = p := hword.1
  · have hunchanged : setBit c.tape c.h true (x+1) = c.tape (x+1) := by
      simp [setBit,show x+1 ≠ c.h by omega]
    calc
      c.tape (x+1) = setBit c.tape c.h true (x+1) := hunchanged.symm
      _ = q := hword.2.1
  · have hunchanged : setBit c.tape c.h true (x+2) = c.tape (x+2) := by
      simp [setBit,show x+2 ≠ c.h by omega]
    calc
      c.tape (x+2) = setBit c.tape c.h true (x+2) := hunchanged.symm
      _ = r := hword.2.2.1
  · have hunchanged : setBit c.tape c.h true (x+3) = c.tape (x+3) := by
      simp [setBit,show x+3 ≠ c.h by omega]
    calc
      c.tape (x+3) = setBit c.tape c.h true (x+3) := hunchanged.symm
      _ = false := hword.2.2.2

theorem noLeft4_excludes_BBad (b : Conf)
    (hb : NoLeft4 true true false b) : ¬ BBad b := by
  intro hbad
  rcases hbad with ⟨_,r,_,hzero0,hzero1,hone1,hone2⟩
  let x : Int := b.h-4-(r:Int)
  have hx : x+3 < b.h := by dsimp [x]; omega
  have hword : b.tape x = true ∧ b.tape (x+1) = true ∧
      b.tape (x+2) = false ∧ b.tape (x+3) = false := by
    dsimp [x]
    refine ⟨hone2,?_,?_,?_⟩
    · have hidx : b.h-4-(r:Int)+1 = b.h-3-(r:Int) := by omega
      rw [hidx]
      exact hone1
    · have hidx : b.h-4-(r:Int)+2 = b.h-2-(r:Int) := by omega
      rw [hidx]
      exact hzero1
    · have hidx : b.h-4-(r:Int)+3 = b.h-1-(r:Int) := by omega
      rw [hidx]
      exact hzero0
  exact hb x hx hword

/-- The alternating F/B retreat preserves the 1100-exclusion shield.
    The wave and B/1-to-F/0 step modify only cells to the right of the new
    retreat head; the F/B sweep itself preserves NoLeft4 by FBSweep. -/
theorem oddRetreatResult_preserves_noLeft4
    (n m : Nat) (t : Int → Bool) (h : Int)
    (hshield : NoLeft4 true true false (⟨.F,h,t⟩ : Conf))
    (hfb : ∀ i : Nat, i < m →
      t (h-2-2*(i:Int)) = false ∧
      t (h-3-2*(i:Int)) = true) :
    NoLeft4 true true false (oddRetreatResult n m t h) := by
  let c1 : Conf := ⟨.F,h-2,setBit (oddWaveTape n t h) (h-1) true⟩
  have hleftTape (x : Int) (hx : x ≤ h-2) : c1.tape x = t x := by
    have hne : x ≠ h-1 := by omega
    have hx' : x < h := by omega
    change setBit (oddWaveTape n t h) (h-1) true x = t x
    simp [setBit,hne,oddWaveTape_left n t h x hx']
  have hNoC1 : NoLeft4 true true false c1 :=
    noLeft4_transfer_of_left_agreement true true false
      (⟨.F,h,t⟩ : Conf) c1
      (by simp [c1]; omega)
      (by intro x hx; exact hleftTape x (by simp [c1] at hx; omega))
      hshield
  have hfbExt : fbExtended m c1 := by
    refine ⟨rfl,?_⟩
    intro i hi
    constructor
    · change c1.tape (h-2-2*(i:Int)) = false
      rw [hleftTape (h-2-2*(i:Int)) (by omega)]
      exact (hfb i hi).1
    · have hpos : c1.h-2*(i:Int)-1 = h-3-2*(i:Int) := by
        simp [c1]
        omega
      change c1.tape (c1.h-2*(i:Int)-1) = true
      rw [hpos,hleftTape (h-3-2*(i:Int)) (by omega)]
      exact (hfb i hi).2
  have hNoFB : NoLeft4 true true false (fbMany m c1) :=
    fb_many_preserves_noLeft4 true true false m c1 hfbExt hNoC1
  let c2 : Conf := fbMany m c1
  have hEq : oddRetreatResult n m t h =
      ⟨.B,c2.h-1,setBit c2.tape c2.h true⟩ := by
    cases hFB : fbMany m c1 with
    | mk q2 h2 t2 =>
      have hq2 : q2 = .F := by
        simpa [hFB,c1] using (fbMany_state m c1 rfl)
      have hh2 : h2 = h-2-2*(m:Int) := by
        have hproj : (fbMany m c1).h = h2 := congrArg Conf.h hFB
        have hhead : (fbMany m c1).h = h-2-2*(m:Int) := by
          simpa [c1] using (fbMany_head m c1)
        exact hproj.symm.trans hhead
      subst q2
      subst h2
      simp only [oddRetreatResult,c1,c2]
      rw [hFB]
      have hhead : h-3-2*(m:Int) = (h-2-2*(m:Int))-1 := by omega
      rw [hhead]
  rw [hEq]
  exact noLeft4_left_write true true false c2 hNoFB

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
    ∃ bout : Conf, run (8*n1+2*m+30) b = some bout ∧
      Reach bout ∧ BZero bout ∧
      (NoLeft4 true true false b → NoLeft4 true true false bout) := by
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
      change twoWavePrefixTape b.tape b.h (b.h+1+(k:Int)) = true
      rw [hp]
      exact hones1 k hk
  have hzero1' : t1 (H+2*(n1:Int)+2) = false := by
    have hidx : H+2*(n1:Int)+2 = b.h+(2*n1+1:Int) := by dsimp [H]; omega
    rw [hidx]
    have hp := twoWavePrefixTape_right b.tape b.h (b.h+(2*n1+1:Int)) (by omega)
    change twoWavePrefixTape b.tape b.h (b.h+(2*n1+1:Int)) = false
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
      have hidx : H-2+1+((0:Nat):Int) = H-1 := by omega
      rw [hidx]
      dsimp [t2]
      simp [setBit]
    · by_cases hj1 : j = 1
      · subst j
        have hidx : H-2+1+((1:Nat):Int) = H := by omega
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
  have hleftTape : ∀ x : Int, x ≤ b.h-4 → t2 x = b.tape x := by
    intro x hx
    have ha := twoWaveAfterFirst_left n1 t1 H x (by dsimp [H]; omega)
    have hp := twoWavePrefixTape_left b.tape b.h x hx
    change (setBit (oddWaveTape n1 t1 H) (H-1) true) x = b.tape x
    rw [ha]
    change twoWavePrefixTape b.tape b.h x = b.tape x
    exact hp
  have hleft2' : t2 (H-2-1) = true := by
    have hidx : H-2-1 = b.h-4 := by dsimp [H]; omega
    rw [hidx]
    rw [hleftTape (b.h-4) (by omega)]
    exact hleft2
  have hfb2 : ∀ i : Nat, i < m →
      t2 ((H-2)-2-2*(i:Int)) = false ∧
      t2 ((H-2)-3-2*(i:Int)) = true := by
    intro i hi
    constructor
    · have hidx : (H-2)-2-2*(i:Int) = b.h-5-2*(i:Int) := by dsimp [H]; omega
      rw [hidx]
      rw [hleftTape (b.h-5-2*(i:Int)) (by omega)]
      exact (hfb i hi).1
    · have hidx : (H-2)-3-2*(i:Int) = b.h-6-2*(i:Int) := by dsimp [H]; omega
      rw [hidx]
      rw [hleftTape (b.h-6-2*(i:Int)) (by omega)]
      exact (hfb i hi).2
  have hfinalF2 : t2 ((H-2)-2-2*(m:Int)) = false := by
    have hidx : (H-2)-2-2*(m:Int) = b.h-5-2*(m:Int) := by dsimp [H]; omega
    rw [hidx]
    rw [hleftTape (b.h-5-2*(m:Int)) (by omega)]
    exact hfinalF
  have hfinalB2 : t2 ((H-2)-3-2*(m:Int)) = false := by
    have hidx : (H-2)-3-2*(m:Int) = b.h-6-2*(m:Int) := by dsimp [H]; omega
    rw [hidx]
    rw [hleftTape (b.h-6-2*(m:Int)) (by omega)]
    exact hfinalB
  have hchain := odd_f1_two_wave_chain_to_b0 n1 (n1+2) m t1 H
    hhead1 hones1' hzero1' hleft1' hhead2 hones2 hzero2 hleft2' hfb2 hfinalF2 hfinalB2
  let h2 : Int := H-2
  let tWave2 : Int → Bool := oddWaveTape (n1+2) t2 h2
  let c3 : Conf := ⟨.F,h2-2,setBit tWave2 (h2-1) true⟩
  have hc3Tape : ∀ x : Int, x ≤ h2-2 → c3.tape x = t2 x := by
    intro x hx
    have hw := oddWaveTape_left (n1+2) t2 h2 x (by omega)
    have hne : x ≠ h2-1 := by omega
    change setBit (oddWaveTape (n1+2) t2 h2) (h2-1) true x = t2 x
    simp [setBit,hne,hw]
  have hc3Left : ∀ x : Int, x < c3.h → c3.tape x = b.tape x := by
    intro x hx
    change x < h2-2 at hx
    have hx2 : x ≤ h2-2 := by omega
    rw [hc3Tape x hx2]
    exact hleftTape x (by dsimp [c3,h2,H] at hx; omega)
  have hfbExt : fbExtended m c3 := by
    refine ⟨rfl,?_⟩
    intro i hi
    constructor
    · have hidx : c3.h-2*(i:Int) = (H-2)-2-2*(i:Int) := by
        dsimp [c3,h2]
      rw [hidx]
      rw [hc3Tape ((H-2)-2-2*(i:Int)) (by omega)]
      exact (hfb2 i hi).1
    · have hidx : c3.h-2*(i:Int)-1 = (H-2)-3-2*(i:Int) := by
        dsimp [c3,h2]
        omega
      rw [hidx]
      rw [hc3Tape ((H-2)-3-2*(i:Int)) (by omega)]
      exact (hfb2 i hi).2
  let c4 : Conf := fbMany m c3
  have hheadC4 : c4.h = h2-2-2*(m:Int) := by
    simpa [c4,c3,h2] using fbMany_head m c3
  let out : Conf := oddRetreatResult (n1+2) m t2 (H-2)
  have hEq : out = ⟨.B,c4.h-1,setBit c4.tape c4.h true⟩ := by
    cases hFB : fbMany m c3 with
    | mk q4 h4 t4 =>
      have hq4 : q4 = .F := by
        simpa [hFB,c3] using (fbMany_state m c3 rfl)
      have hh4 : h4 = h2-2-2*(m:Int) := by
        have hproj : (fbMany m c3).h = h4 := congrArg Conf.h hFB
        have hhead : (fbMany m c3).h = h2-2-2*(m:Int) := by
          simpa [c3,h2] using (fbMany_head m c3)
        exact hproj.symm.trans hhead
      subst q4
      subst h4
      simp only [out,oddRetreatResult,c4,c3,h2,tWave2]
      rw [hFB]
      have hhead : H-2-3-2*(m:Int) = (H-2-2-2*(m:Int))-1 := by omega
      rw [hhead]
  have hNoOut : NoLeft4 true true false b → NoLeft4 true true false out := by
    intro hshield
    have hNoC3 : NoLeft4 true true false c3 :=
      noLeft4_transfer_of_left_agreement true true false b c3
        (by dsimp [c3,h2,H]; omega) hc3Left hshield
    have hNoFB : NoLeft4 true true false (fbMany m c3) :=
      fb_many_preserves_noLeft4 true true false m c3 hfbExt hNoC3
    rw [hEq]
    exact noLeft4_left_write true true false c4 hNoFB
  have htotal : 8*n1+2*m+30 =
      9+(4*n1+4*(n1+2)+2*m+13) := by omega
  have hadd := run_add 9 (4*n1+4*(n1+2)+2*m+13) b
  have hrun : run (8*n1+2*m+30) b = some out := by
    rw [htotal,hadd,hprefix]
    simp only [Option.bind_some]
    simpa [out,t2] using hchain.1
  have houtReach : Reach out :=
    reachable_of_run (8*n1+2*m+30) b out hb hrun
  have houtB : BZero out := by
    refine ⟨rfl,?_⟩
    simpa [out,oddRetreatResult,t2] using hchain.2
  exact ⟨out,hrun,houtReach,houtB,hNoOut⟩

/-- Under the BShield invariant, a completed two-wave root interval cannot
    end at the BBad gate: BBad contains the forbidden left factor 1100. -/
theorem b0_two_wave_root_interval_avoids_BBad
    (b : Conf) (n1 m : Nat)
    (hb : Reach b) (hb0 : BZero b)
    (hshield : NoLeft4 true true false b)
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
    ∃ bout : Conf, run (8*n1+2*m+30) b = some bout ∧
      Reach bout ∧ BZero bout ∧ ¬ BBad bout := by
  obtain ⟨bout,hrun,hreach,hbOut,hpreserve⟩ :=
    b0_two_wave_root_interval_to_b0 b n1 m hb hb0
      hleft0 hzero0 hone0 hleft2 hfb hfinalF hfinalB hones1 hzero1 hextra hzero2
  exact ⟨bout,hrun,hreach,hbOut,noLeft4_excludes_BBad bout (hpreserve hshield)⟩

#print axioms BB6Root119.b0_two_wave_prefix
#print axioms BB6Root119.b0_two_wave_root_interval_to_b0
#print axioms BB6Root119.b0_two_wave_root_interval_avoids_BBad
#print axioms BB6Root119.noLeft4_excludes_BBad
#print axioms BB6Root119.oddRetreatResult_preserves_noLeft4

end BB6Root119
