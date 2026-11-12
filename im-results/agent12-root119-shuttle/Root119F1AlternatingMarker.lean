import Root119OddWaveRetreat
import Root119WaveMarkerShield
import Root119BShield
import Root119FBSweep

namespace BB6Root119

/-- The m alternating F/0-B/1 retreat pairs fill the entire interval
    immediately to the right of their final F head.  The final head itself
    is not touched. -/
theorem fb_many_fills_interval (m : Nat) (c : Conf)
    (hv : fbExtended m c) :
    ∀ x : Int, c.h - 2*(m:Int) < x → x ≤ c.h →
      (fbMany m c).tape x = true := by
  induction m generalizing c with
  | zero =>
      intro x hx _
      omega
  | succ m ih =>
      intro x hx hupper
      have htail := fbExtended_tail m c hv
      change (fbMany m (fbPair c)).tape x = true
      by_cases hx0 : x = c.h
      · subst x
        have hnot : ¬ fbTouched m (fbPair c) c.h := by
          rintro ⟨i,hi,heq⟩
          change c.h = c.h-2-2*(i:Int) at heq
          omega
        rw [fb_many_unvisited m (fbPair c) c.h hnot]
        simp [fbPair,setBit]
      · by_cases hx1 : x = c.h-1
        · subst x
          have hnot : ¬ fbTouched m (fbPair c) (c.h-1) := by
            rintro ⟨i,hi,heq⟩
            change c.h-1 = c.h-2-2*(i:Int) at heq
            omega
          rw [fb_many_unvisited m (fbPair c) (c.h-1) hnot]
          have hbit := (hv.2 0 (by omega)).2
          simpa [fbPair,setBit,show c.h-1 ≠ c.h by omega] using hbit
        · have hlow : (fbPair c).h - 2*(m:Int) < x := by
            change c.h-2-2*(m:Int) < x
            omega
          have hhigh : x ≤ (fbPair c).h := by
            change x ≤ c.h-2
            omega
          exact ih (fbPair c) htail x hlow hhigh

/-- The odd-wave normal form changes no cell at or beyond its right boundary. -/
theorem oddWaveTape_outside_right (n : Nat) (t : Int → Bool) (h x : Int)
    (hx : h+2*(n:Int)+3 ≤ x) : oddWaveTape n t h x = t x := by
  have hout := shuttleFill_outside (setBit t h false) (h+1) x (2*n+2)
    (Or.inr (by omega))
  have hne : x ≠ h := by omega
  simp [oddWaveTape,setBit,hne,hout]

/-- For n=0 the odd F/1 wave fills h+1 and h+2. -/
theorem oddWaveTape_zero_ones (t : Int → Bool) (h : Int) :
    oddWaveTape 0 t h (h+1) = true ∧
    oddWaveTape 0 t h (h+2) = true := by
  constructor <;> simp [oddWaveTape,shuttleFill,setBit] <;> omega

/-- Exact endpoint of an n=0 F/1 wave followed by m alternating
    F/0-B/1 retreat pairs.  The retreat preserves the entire tape at and
    left of its final F head, fills the corridor to h-2, and leaves the
    right tail from h+3 unchanged. -/
theorem odd_f1_retreat_endpoint (m : Nat) (t : Int → Bool) (h : Int)
    (hhead : t h = true)
    (hleft : t (h-1) = true)
    (hright1 : t (h+1) = true)
    (hright2 : t (h+2) = false)
    (hfb : ∀ i : Nat, i < m →
      t (h-2-2*(i:Int)) = false ∧ t (h-3-2*(i:Int)) = true)
    (hfinalF : t (h-2-2*(m:Int)) = true)
    (hfinalB : t (h-3-2*(m:Int)) = false) :
    ∃ f, run (2*m+6) (⟨.F,h,t⟩ : Conf) = some f ∧
      f.q = .F ∧
      f.h = h-2-2*(m:Int) ∧
      f.tape f.h = true ∧
      f.tape (f.h-1) = false ∧
      (∀ x : Int, x ≤ f.h → f.tape x = t x) ∧
      (∀ x : Int, f.h < x → x ≤ h-2 → f.tape x = true) ∧
      (∀ x : Int, h+3 ≤ x → f.tape x = t x) ∧
      f.tape (h-1) = true ∧
      f.tape h = true ∧
      f.tape (h+1) = true ∧
      f.tape (h+2) = true := by
  let waveTape := oddWaveTape 0 t h
  let c1 : Conf := ⟨.F,h-2,setBit waveTape (h-1) true⟩
  have hones : ∀ j : Nat, j < 1 → t (h+1+(j:Int)) = true := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simpa using hright1
  have hwave := odd_f1_to_b 0 t h hhead hones hright2
  have hwleft : waveTape (h-1) = true := by
    change oddWaveTape 0 t h (h-1) = true
    rw [oddWaveTape_left 0 t h (h-1) (by omega)]
    exact hleft
  have hBstep : run 1 (⟨.B,h-1,waveTape⟩ : Conf) = some c1 := by
    have hpos : h-1-1 = h-2 := by omega
    simp [run,next,c1,hwleft,hpos]
  have hleftTape (x : Int) (hx : x ≤ h-2) : c1.tape x = t x := by
    have hne : x ≠ h-1 := by omega
    have hx' : x < h := by omega
    change setBit (oddWaveTape 0 t h) (h-1) true x = t x
    simp [setBit,hne,oddWaveTape_left 0 t h x hx']
  have hfb' : fbExtended m c1 := by
    constructor
    · rfl
    · intro i hi
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
  have hfbRun : run (2*m) c1 = some (fbMany m c1) :=
    fb_two_n m c1 hfb'
  have hnotF : ¬ fbTouched m c1 (h-2-2*(m:Int)) := by
    intro hx
    rcases hx with ⟨i,hi,heq⟩
    change h-2-2*(m:Int) = (h-2)-2*(i:Int) at heq
    omega
  have hnotB : ¬ fbTouched m c1 (h-3-2*(m:Int)) := by
    intro hx
    rcases hx with ⟨i,hi,heq⟩
    change h-3-2*(m:Int) = (h-2)-2*(i:Int) at heq
    omega
  have hFread : (fbMany m c1).tape (h-2-2*(m:Int)) = true := by
    rw [fb_many_unvisited m c1 _ hnotF]
    rw [hleftTape (h-2-2*(m:Int)) (by omega)]
    exact hfinalF
  have hBread : (fbMany m c1).tape (h-3-2*(m:Int)) = false := by
    rw [fb_many_unvisited m c1 _ hnotB]
    rw [hleftTape (h-3-2*(m:Int)) (by omega)]
    exact hfinalB
  have hrun : run (2*m+6) (⟨.F,h,t⟩ : Conf) = some (fbMany m c1) := by
    have htotal : 2*m+6 = 5+(1+2*m) := by omega
    have hd := run_add 5 (1+2*m) (⟨.F,h,t⟩ : Conf)
    rw [htotal,hd,hwave]
    simp only [Option.bind_some]
    have hd2 := run_add 1 (2*m) (⟨.B,h-1,waveTape⟩ : Conf)
    rw [hd2,hBstep]
    simp only [Option.bind_some]
    exact hfbRun
  let f : Conf := fbMany m c1
  have hfq : f.q = .F := by
    simpa [f] using fbMany_state m c1 rfl
  have hfhead : f.h = h-2-2*(m:Int) := by
    simpa [f,c1] using fbMany_head m c1
  have hleftPres : ∀ x : Int, x ≤ h-2-2*(m:Int) → f.tape x = t x := by
    intro x hx
    have hnot : ¬ fbTouched m c1 x := by
      rintro ⟨i,hi,heq⟩
      change x = (h-2)-2*(i:Int) at heq
      omega
    change (fbMany m c1).tape x = t x
    rw [fb_many_unvisited m c1 x hnot]
    exact hleftTape x (by omega)
  have hinterval : ∀ x : Int, h-2-2*(m:Int) < x → x ≤ h-2 →
      f.tape x = true := by
    intro x hxlo hxhi
    have hlow : c1.h-2*(m:Int) < x := by simp [c1]; omega
    have hhigh : x ≤ c1.h := by simp [c1]; exact hxhi
    have hfill := fb_many_fills_interval m c1 hfb' x hlow hhigh
    simpa [f] using hfill
  have hrightPres : ∀ x : Int, h-2 < x →
      f.tape x = setBit waveTape (h-1) true x := by
    intro x hx
    have hp := fb_many_preserves_right m c1 x (by simp [c1]; omega)
    simpa [f,c1] using hp
  have hrightTail : ∀ x : Int, h+3 ≤ x → f.tape x = t x := by
    intro x hx
    rw [hrightPres x (by omega)]
    have hne : x ≠ h-1 := by omega
    simp only [setBit,if_neg hne]
    exact oddWaveTape_outside_right 0 t h x (by omega)
  have hAtLeft : f.tape (h-1) = true := by
    rw [hrightPres (h-1) (by omega)]
    simp [setBit]
  have hAtHead : f.tape h = true := by
    rw [hrightPres h (by omega)]
    simp [setBit,oddWaveTape]
  have hwaveOnes := oddWaveTape_zero_ones t h
  have hAtH1 : f.tape (h+1) = true := by
    rw [hrightPres (h+1) (by omega)]
    have hne : h+1 ≠ h-1 := by omega
    simpa [setBit,hne] using hwaveOnes.1
  have hAtH2 : f.tape (h+2) = true := by
    rw [hrightPres (h+2) (by omega)]
    have hne : h+2 ≠ h-1 := by omega
    simpa [setBit,hne] using hwaveOnes.2
  refine ⟨f,?_,hfq,hfhead,?_,?_,?_,?_,hrightTail,hAtLeft,hAtHead,hAtH1,hAtH2⟩
  · simpa [f] using hrun
  · rw [hleftPres f.h (by rw [hfhead]; omega)]
    rw [hfhead]
    exact hfinalF
  · rw [hleftPres (f.h-1) (by rw [hfhead]; omega)]
    rw [hfhead]
    exact hfinalB
  · intro x hx
    exact hleftPres x (by rw [hfhead] at hx; exact hx)
  · intro x hxlo hxhi
    exact hinterval x (by rw [hfhead] at hxlo; exact hxlo) hxhi

/-- A two-sided alternating F1 retreat can create a temporary 1100 marker,
    then the exact odd-wave return removes it and restores the B/0 shield.
    The total source-machine cost is 6m+19 primitive transitions. -/
theorem alternating_f1_marker_return (m : Nat) (t : Int → Bool) (h : Int)
    (hc : Reach (⟨.F,h,t⟩ : Conf))
    (hhead : t h = true)
    (hleft : t (h-1) = true)
    (hright1 : t (h+1) = true)
    (hright2 : t (h+2) = false)
    (hright3 : t (h+3) = true)
    (hright4 : t (h+4) = false)
    (hfb : ∀ i : Nat, i < m →
      t (h-2-2*(i:Int)) = false ∧ t (h-3-2*(i:Int)) = true)
    (hfinalF : t (h-2-2*(m:Int)) = true)
    (hfinalB : t (h-3-2*(m:Int)) = false)
    (hfinal2 : t (h-4-2*(m:Int)) = true)
    (hfinal3 : t (h-5-2*(m:Int)) = true)
    (hn : noLeft1100 (⟨.F,h,t⟩ : Conf)) :
    ∃ f d b,
      run (2*m+6) (⟨.F,h,t⟩ : Conf) = some f ∧
      Reach f ∧
      f.q = .F ∧ f.h = h-2-2*(m:Int) ∧
      f.tape f.h = true ∧
      f.tape (f.h-1) = false ∧
      f.tape (f.h-2) = true ∧
      f.tape (f.h-3) = true ∧
      noLeft1100 f ∧
      (∀ j : Nat, j < 2*m+5 →
        f.tape (f.h+1+(j:Int)) = true) ∧
      f.tape (f.h+2*(m+2:Int)+2) = false ∧
      next f = some d ∧
      Reach d ∧ d.q = .D ∧ d.h = f.h+1 ∧
      d.tape (f.h-3) = true ∧
      d.tape (f.h-2) = true ∧
      d.tape (f.h-1) = false ∧
      d.tape f.h = false ∧
      run (4*m+13) f = some b ∧
      run (6*m+19) (⟨.F,h,t⟩ : Conf) = some b ∧
      Reach b ∧ BZero b ∧ b.h = f.h-1 ∧ noLeft1100 b := by
  obtain ⟨f,hrun1,hfq,hfhead,hfcur,hfleft,hleftPres,hinterval,hrightTail,
      hAtLeft,hAtHead,hAtH1,hAtH2⟩ :=
    odd_f1_retreat_endpoint m t h hhead hleft hright1 hright2 hfb hfinalF hfinalB
  have hf3 : f.tape (f.h-3) = true := by
    rw [hleftPres (f.h-3) (by rw [hfhead]; omega)]
    rw [hfhead]
    exact hfinal3
  have hf2 : f.tape (f.h-2) = true := by
    rw [hleftPres (f.h-2) (by rw [hfhead]; omega)]
    rw [hfhead]
    exact hfinal2
  have hnF : noLeft1100 f := by
    intro x hx hpat
    have h0 := hleftPres x (by rw [hfhead] at hx; omega)
    have h1 := hleftPres (x+1) (by rw [hfhead] at hx; omega)
    have h2 := hleftPres (x+2) (by rw [hfhead] at hx; omega)
    have h3 := hleftPres (x+3) (by rw [hfhead] at hx; omega)
    have hpat' : t x = true ∧ t (x+1) = true ∧
        t (x+2) = false ∧ t (x+3) = false := by
      exact ⟨by rw [←h0]; exact hpat.1,
        by rw [←h1]; exact hpat.2.1,
        by rw [←h2]; exact hpat.2.2.1,
        by rw [←h3]; exact hpat.2.2.2⟩
    exact hn x (by rw [hfhead] at hx; omega) hpat'
  have honesF : ∀ j : Nat, j < 2*m+5 →
      f.tape (f.h+1+(j:Int)) = true := by
    intro j hj
    have hx : f.h+1+(j:Int) ≤ h+3 := by rw [hfhead]; omega
    have hxgt : f.h < f.h+1+(j:Int) := by omega
    by_cases hleftRange : f.h+1+(j:Int) ≤ h-2
    · exact hinterval _ hxgt hleftRange
    · have hcases : f.h+1+(j:Int) = h-1 ∨
          f.h+1+(j:Int) = h ∨
          f.h+1+(j:Int) = h+1 ∨
          f.h+1+(j:Int) = h+2 ∨
          f.h+1+(j:Int) = h+3 := by
        rw [hfhead] at *
        omega
      rcases hcases with h0|h1|h2|h3|h4
      · rw [h0]; exact hAtLeft
      · rw [h1]; exact hAtHead
      · rw [h2]; exact hAtH1
      · rw [h3]; exact hAtH2
      · rw [h4]
        rw [hrightTail (h+3) (by omega)]
        exact hright3
  have hterm : f.tape (f.h+2*(m+2:Int)+2) = false := by
    have hidx : f.h+2*(m+2:Int)+2 = h+4 := by
      rw [hfhead]
      omega
    rw [hidx,hrightTail (h+4) (by omega)]
    exact hright4
  have honesWave : ∀ j : Nat, j < 2*(m+2)+1 →
      f.tape (f.h+1+(j:Int)) = true := by
    intro j hj
    apply honesF j
    omega
  have hv : waveValid (m+2) f := ⟨hfq,hfcur,hfleft,honesWave,hterm⟩
  let d : Conf := ⟨.D,f.h+1,setBit f.tape f.h false⟩
  have hnext : next f = some d := by
    cases f with
    | mk q pos tape =>
      have hq : q = .F := hfq
      have hb : tape pos = true := hfcur
      simp [next,hq,hb,d]
  have hd3 : d.tape (f.h-3) = true := by
    change setBit f.tape f.h false (f.h-3) = true
    have hne : f.h-3 ≠ f.h := by omega
    simp [setBit,hne,hf3]
  have hd2 : d.tape (f.h-2) = true := by
    change setBit f.tape f.h false (f.h-2) = true
    have hne : f.h-2 ≠ f.h := by omega
    simp [setBit,hne,hf2]
  have hd1 : d.tape (f.h-1) = false := by
    change setBit f.tape f.h false (f.h-1) = false
    have hne : f.h-1 ≠ f.h := by omega
    simp [setBit,hne,hfleft]
  have hd0 : d.tape f.h = false := by
    change setBit f.tape f.h false f.h = false
    simp [setBit]
  let b : Conf := waveMarkerOut (m+2) f
  have hwave := wave_marker_run (m+2) f hv
  have htime : 4*m+13 = 4*(m+2)+5 := by omega
  have hrun2 : run (4*m+13) f = some b := by
    rw [htime]
    simpa [b] using hwave
  have hnB : noLeft1100 b :=
    wave_marker_preserves_noLeft1100 (m+2) f hv hnF
  have hbHead : b.h = f.h-1 := rfl
  have hbZero : BZero b := by
    constructor
    · rfl
    · change setBit f.tape (f.h+2*(m+2:Int)+2) true (f.h-1) = false
      have hne : f.h-1 ≠ f.h+2*(m+2:Int)+2 := by omega
      simp [setBit,hne,hfleft]
  have hreachF : Reach f :=
    reachable_of_run (2*m+6) (⟨.F,h,t⟩ : Conf) f hc hrun1
  have hreachD : Reach d := Reach.follow hreachF hnext
  have htimeTotal : 6*m+19 = (2*m+6)+(4*m+13) := by omega
  have htotal := run_add (2*m+6) (4*m+13) (⟨.F,h,t⟩ : Conf)
  have hrunTotal : run (6*m+19) (⟨.F,h,t⟩ : Conf) = some b := by
    rw [htimeTotal,htotal,hrun1]
    simp only [Option.bind_some]
    exact hrun2
  have hreachB : Reach b :=
    reachable_of_run (6*m+19) (⟨.F,h,t⟩ : Conf) b hc hrunTotal
  refine ⟨f,d,b,hrun1,hreachF,hfq,hfhead,hfcur,hfleft,hf2,hf3,hnF,
    honesF,hterm,hnext,hreachD,rfl,rfl,hd3,hd2,hd1,hd0,
    hrun2,hrunTotal,hreachB,hbZero,hbHead,hnB⟩

#print axioms BB6Root119.fb_many_fills_interval
#print axioms BB6Root119.odd_f1_retreat_endpoint
#print axioms BB6Root119.alternating_f1_marker_return

end BB6Root119
