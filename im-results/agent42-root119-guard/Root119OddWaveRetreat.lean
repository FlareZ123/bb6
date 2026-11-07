import Root119Shuttle
import Root119WaveNormal
import Root119BRegular
namespace BB6Root119

theorem run_eq_shuttleRun (n : Nat) (c : Conf) :
    run n c = shuttleRun n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    change (next c).bind (run n) = (next c).bind (shuttleRun n)
    cases next c with
    | none => rfl
    | some d => simp [ih]

def oddWaveTape (n : Nat) (t : Int → Bool) (h : Int) : Int → Bool :=
  setBit (shuttleFill (setBit t h false) (h+1) (2*n+2)) h true

theorem oddWaveTape_left (n : Nat) (t : Int → Bool) (h x : Int)
    (hx : x < h) : oddWaveTape n t h x = t x := by
  have hout := shuttleFill_outside (setBit t h false) (h+1) x (2*n+2)
    (Or.inl (by omega))
  have hne : x ≠ h := by omega
  simp [oddWaveTape,setBit,hne,hout]

/-- An odd rightward run from F/1 returns to B one cell left, independently
    of the tape to the left. -/
theorem odd_f1_to_b (n : Nat) (t : Int → Bool) (h : Int)
    (hhead : t h = true)
    (hones : ∀ j : Nat, j < 2*n+1 → t (h+1+(j:Int)) = true)
    (hzero : t (h+2*(n:Int)+2) = false) :
    run (4*n+5) (⟨.F,h,t⟩ : Conf) =
      some ⟨.B,h-1,oddWaveTape n t h⟩ := by
  have hfirst : run 1 (⟨.F,h,t⟩ : Conf) =
      some ⟨.D,h+1,setBit t h false⟩ := by
    simp [run,next,hhead]
  have hones' : ∀ j : Nat, j < 2*n+1 →
      (setBit t h false) (h+1+(j:Int)) = true := by
    intro j hj
    have hne : h+1+(j:Int) ≠ h := by omega
    simpa [setBit,hne] using hones j hj
  have hzero' : (setBit t h false) (h+1+(2*n+1:Int)) = false := by
    have hne : h+1+(2*n+1:Int) ≠ h := by omega
    have heq : h+1+(2*n+1:Int) = h+2*(n:Int)+2 := by omega
    rw [show h+1+(2*n+1:Int) = h+2*(n:Int)+2 by omega]
    simpa [setBit,show h+2*(n:Int)+2 ≠ h by omega] using hzero
  have hshuttle := shuttle n (setBit t h false) (h+1) hones' hzero'
  have hshuttle' : run (4*n+3)
      (⟨.D,h+1,setBit t h false⟩ : Conf) =
      some ⟨.F,h,shuttleFill (setBit t h false) (h+1) (2*n+2)⟩ := by
    rw [run_eq_shuttleRun]
    have hpos : h+1-1 = h := by omega
    simpa [hpos] using hshuttle
  have hFzero : (shuttleFill (setBit t h false) (h+1) (2*n+2)) h = false := by
    rw [shuttleFill_outside]
    · simp [setBit]
    · exact Or.inl (by omega)
  have hlast : run 1
      (⟨.F,h,shuttleFill (setBit t h false) (h+1) (2*n+2)⟩ : Conf) =
      some ⟨.B,h-1,oddWaveTape n t h⟩ := by
    simp [run,next,hFzero,oddWaveTape]
  have htime : 4*n+5 = 1+((4*n+3)+1) := by omega
  have hdecomp1 := run_add 1 ((4*n+3)+1) (⟨.F,h,t⟩ : Conf)
  rw [htime,hdecomp1,hfirst]
  simp only [Option.bind_some]
  have hdecomp2 := run_add (4*n+3) 1
    (⟨.D,h+1,setBit t h false⟩ : Conf)
  rw [hdecomp2,hshuttle']
  simp only [Option.bind_some]
  exact hlast

theorem fbMany_state (n : Nat) (c : Conf) (hq : c.q = .F) :
    (fbMany n c).q = .F := by
  induction n generalizing c with
  | zero => simpa [fbMany] using hq
  | succ n ih =>
    simpa [fbMany,fbPair] using ih (fbPair c) rfl

/-- A general odd F/1 wave followed by an arbitrary finite alternating
    B/1-F/0 retreat, terminating at the first specified B/0. -/
theorem odd_f1_retreat_to_b0 (n m : Nat) (t : Int → Bool) (h : Int)
    (hhead : t h = true)
    (hones : ∀ j : Nat, j < 2*n+1 → t (h+1+(j:Int)) = true)
    (hzero : t (h+2*(n:Int)+2) = false)
    (hleft : t (h-1) = true)
    (hfb : ∀ i : Nat, i < m →
      t (h-2-2*(i:Int)) = false ∧ t (h-3-2*(i:Int)) = true)
    (hfinalF : t (h-2-2*(m:Int)) = false)
    (hfinalB : t (h-3-2*(m:Int)) = false) :
    run (4*n+2*m+7) (⟨.F,h,t⟩ : Conf) =
      some ⟨.B,h-3-2*(m:Int),
        setBit (fbMany m
          (⟨.F,h-2,setBit (oddWaveTape n t h) (h-1) true⟩ : Conf)).tape
          (h-2-2*(m:Int)) true⟩ ∧
    (setBit (fbMany m
      (⟨.F,h-2,setBit (oddWaveTape n t h) (h-1) true⟩ : Conf)).tape
        (h-2-2*(m:Int)) true) (h-3-2*(m:Int)) = false := by
  let waveTape := oddWaveTape n t h
  let c1 : Conf := ⟨.F,h-2,setBit waveTape (h-1) true⟩
  have hwave := odd_f1_to_b n t h hhead hones hzero
  have hwleft : waveTape (h-1) = true := by
    change oddWaveTape n t h (h-1) = true
    rw [oddWaveTape_left n t h (h-1) (by omega)]
    exact hleft
  have hBstep : run 1 (⟨.B,h-1,waveTape⟩ : Conf) = some c1 := by
    have hpos : h-1-1 = h-2 := by omega
    simp [run,next,c1,hwleft,hpos]
  have hleftTape (x : Int) (hx : x ≤ h-2) : c1.tape x = t x := by
    have hne : x ≠ h-1 := by omega
    have hx' : x < h := by omega
    change setBit (oddWaveTape n t h) (h-1) true x = t x
    simp [setBit,hne,oddWaveTape_left n t h x hx']
  have hfb' : fbExtended m c1 := by
    constructor
    · rfl
    · intro i hi
      constructor
      · change c1.tape (h-2-2*(i:Int)) = false
        rw [hleftTape (h-2-2*(i:Int)) (by omega)]
        exact (hfb i hi).1
      · have hpos : c1.h-2*(i:Int)-1 = h-3-2*(i:Int) := by simp [c1]; omega
        change c1.tape (c1.h-2*(i:Int)-1) = true
        rw [hpos,hleftTape (h-3-2*(i:Int)) (by omega)]
        exact (hfb i hi).2
  have hfbRun : run (2*m) c1 = some (fbMany m c1) := fb_two_n m c1 hfb'
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
  have hFread : (fbMany m c1).tape (h-2-2*(m:Int)) = false := by
    rw [fb_many_unvisited m c1 _ hnotF]
    have heq := hleftTape (h-2-2*(m:Int)) (by omega)
    rw [heq]
    exact hfinalF
  have hBread : (fbMany m c1).tape (h-3-2*(m:Int)) = false := by
    rw [fb_many_unvisited m c1 _ hnotB]
    have heq := hleftTape (h-3-2*(m:Int)) (by omega)
    rw [heq]
    exact hfinalB
  have hlast : run 1 (fbMany m c1) =
      some ⟨.B,h-3-2*(m:Int),
        setBit (fbMany m c1).tape (h-2-2*(m:Int)) true⟩ := by
    have hhead' : (fbMany m c1).h = h-2-2*(m:Int) := by
      simpa [c1] using fbMany_head m c1
    have hhead'' : (fbMany m c1).h = h-(2+2*(m:Int)) := by
      have hidx : h-2-2*(m:Int) = h-(2+2*(m:Int)) := by omega
      rw [hhead',hidx]
    have hq' : (fbMany m c1).q = .F := fbMany_state m c1 rfl
    have hFread'' : (fbMany m c1).tape (h-(2+2*(m:Int))) = false := by
      have hidx : h-(2+2*(m:Int)) = h-2-2*(m:Int) := by omega
      rw [hidx]
      exact hFread
    have hpos'' : h-(2+2*(m:Int))-1 = h-3-2*(m:Int) := by omega
    simp [run,next,hq',hFread'',hhead'',hpos'']
  have hrest : run (1+(2*m+1)) (⟨.B,h-1,waveTape⟩ : Conf) =
      some ⟨.B,h-3-2*(m:Int),
        setBit (fbMany m c1).tape (h-2-2*(m:Int)) true⟩ := by
    have hd1 := run_add 1 (2*m+1) (⟨.B,h-1,waveTape⟩ : Conf)
    rw [hd1,hBstep]
    simp only [Option.bind_some]
    have hd2 := run_add (2*m) 1 c1
    rw [hd2,hfbRun]
    simp only [Option.bind_some]
    exact hlast
  have htotal : 4*n+2*m+7 = (4*n+5)+(1+(2*m+1)) := by omega
  have hd := run_add (4*n+5) (1+(2*m+1)) (⟨.F,h,t⟩ : Conf)
  rw [htotal,hd,hwave]
  simp only [Option.bind_some]
  constructor
  · exact hrest
  · change (setBit (fbMany m c1).tape (h-2-2*(m:Int)) true)
        (h-3-2*(m:Int)) = false
    have hne : h-3-2*(m:Int) ≠ h-2-2*(m:Int) := by omega
    have hBread' : (fbMany m c1).tape (h-(3+2*(m:Int))) = false := by
      have hidx : h-(3+2*(m:Int)) = h-3-2*(m:Int) := by omega
      rw [hidx]
      exact hBread
    simp [setBit,hne,hBread']

def oddRetreatResult (n m : Nat) (t : Int → Bool) (h : Int) : Conf :=
  ⟨.B,h-3-2*(m:Int),
    setBit (fbMany m
      (⟨.F,h-2,setBit (oddWaveTape n t h) (h-1) true⟩ : Conf)).tape
      (h-2-2*(m:Int)) true⟩

/-- Two consecutive odd F/1 waves. The first wave returns B/1, which
    immediately steps left into the second F/1 wave; the second wave then
    performs the general alternating left retreat. -/
theorem odd_f1_two_wave_chain_to_b0 (n1 n2 m : Nat)
    (t : Int → Bool) (h : Int)
    (hhead1 : t h = true)
    (hones1 : ∀ j : Nat, j < 2*n1+1 → t (h+1+(j:Int)) = true)
    (hzero1 : t (h+2*(n1:Int)+2) = false)
    (hleft1 : t (h-1) = true)
    (hhead2 :
      (setBit (oddWaveTape n1 t h) (h-1) true) (h-2) = true)
    (hones2 : ∀ j : Nat, j < 2*n2+1 →
      (setBit (oddWaveTape n1 t h) (h-1) true) (h-2+1+(j:Int)) = true)
    (hzero2 :
      (setBit (oddWaveTape n1 t h) (h-1) true)
        (h-2+2*(n2:Int)+2) = false)
    (hleft2 :
      (setBit (oddWaveTape n1 t h) (h-1) true) (h-2-1) = true)
    (hfb2 : ∀ i : Nat, i < m →
      (setBit (oddWaveTape n1 t h) (h-1) true) ((h-2)-2-2*(i:Int)) = false ∧
      (setBit (oddWaveTape n1 t h) (h-1) true) ((h-2)-3-2*(i:Int)) = true)
    (hfinalF2 :
      (setBit (oddWaveTape n1 t h) (h-1) true) ((h-2)-2-2*(m:Int)) = false)
    (hfinalB2 :
      (setBit (oddWaveTape n1 t h) (h-1) true) ((h-2)-3-2*(m:Int)) = false) :
    run (4*n1+4*n2+2*m+13) (⟨.F,h,t⟩ : Conf) =
      some (oddRetreatResult n2 m
        (setBit (oddWaveTape n1 t h) (h-1) true) (h-2)) ∧
    (oddRetreatResult n2 m
      (setBit (oddWaveTape n1 t h) (h-1) true) (h-2)).tape
      (oddRetreatResult n2 m
        (setBit (oddWaveTape n1 t h) (h-1) true) (h-2)).h = false := by
  let t2 := setBit (oddWaveTape n1 t h) (h-1) true
  have hfirst := odd_f1_to_b n1 t h hhead1 hones1 hzero1
  have hwleft : oddWaveTape n1 t h (h-1) = true := by
    rw [oddWaveTape_left n1 t h (h-1) (by omega)]
    exact hleft1
  have hBstep : run 1 (⟨.B,h-1,oddWaveTape n1 t h⟩ : Conf) =
      some (⟨.F,h-2,t2⟩ : Conf) := by
    simp [run,next,t2,hwleft] <;> omega
  have hprefix : run (4*n1+6) (⟨.F,h,t⟩ : Conf) =
      some (⟨.F,h-2,t2⟩ : Conf) := by
    have htime : 4*n1+6 = (4*n1+5)+1 := by omega
    have hd := run_add (4*n1+5) 1 (⟨.F,h,t⟩ : Conf)
    rw [htime,hd,hfirst]
    simp only [Option.bind_some]
    exact hBstep
  have hsecond := odd_f1_retreat_to_b0 n2 m t2 (h-2)
    hhead2 hones2 hzero2 hleft2 hfb2 hfinalF2 hfinalB2
  have htotal : 4*n1+4*n2+2*m+13 =
      (4*n1+6)+(4*n2+2*m+7) := by omega
  have hd := run_add (4*n1+6) (4*n2+2*m+7) (⟨.F,h,t⟩ : Conf)
  rw [htotal,hd,hprefix]
  simp only [Option.bind_some]
  simpa [oddRetreatResult,t2] using hsecond

/-- An odd D/1 shuttle followed by an arbitrary finite alternating
    F/0-B/1 retreat, terminating at the specified B/0. -/
theorem d1_retreat_to_b0 (n m : Nat) (t : Int → Bool) (h : Int)
    (hones : ∀ j : Nat, j < 2*n+1 → t (h+(j:Int)) = true)
    (hzero : t (h+(2*n+1:Int)) = false)
    (hleftF : t (h-1) = false)
    (hleftB : t (h-2) = true)
    (hfb : ∀ i : Nat, i < m →
      t (h-3-2*(i:Int)) = false ∧ t (h-4-2*(i:Int)) = true)
    (hfinalF : t (h-3-2*(m:Int)) = false)
    (hfinalB : t (h-4-2*(m:Int)) = false) :
    run (4*n+2*m+6) (⟨.D,h,t⟩ : Conf) =
      some ⟨.B,h-4-2*(m:Int),
        setBit (fbMany m
          (⟨.F,h-3,
            setBit (setBit (shuttleFill t h (2*n+2)) (h-1) true)
              (h-2) true⟩ : Conf)).tape
          (h-3-2*(m:Int)) true⟩ ∧
    (setBit (fbMany m
      (⟨.F,h-3,
        setBit (setBit (shuttleFill t h (2*n+2)) (h-1) true)
          (h-2) true⟩ : Conf)).tape
        (h-3-2*(m:Int)) true) (h-4-2*(m:Int)) = false := by
  let c1 : Conf := ⟨.F,h-3,
    setBit (setBit (shuttleFill t h (2*n+2)) (h-1) true)
      (h-2) true⟩
  have hsh := shuttle n t h hones hzero
  have hsh' : run (4*n+3) (⟨.D,h,t⟩ : Conf) =
      some ⟨.F,h-1,shuttleFill t h (2*n+2)⟩ := by
    rw [run_eq_shuttleRun]
    exact hsh
  have hFstep : run 1
      (⟨.F,h-1,shuttleFill t h (2*n+2)⟩ : Conf) =
      some ⟨.B,h-2,setBit (shuttleFill t h (2*n+2)) (h-1) true⟩ := by
    have hread := shuttleFill_outside t h (h-1) (2*n+2) (Or.inl (by omega))
    simp [run,next,hread,hleftF] <;> omega
  have hBread : (setBit (shuttleFill t h (2*n+2)) (h-1) true) (h-2) = true := by
    have hread := shuttleFill_outside t h (h-2) (2*n+2) (Or.inl (by omega))
    have hne : h-2 ≠ h-1 := by omega
    simp [setBit,hne,hread,hleftB]
  have hBstep : run 1
      (⟨.B,h-2,setBit (shuttleFill t h (2*n+2)) (h-1) true⟩ : Conf) =
      some c1 := by
    have hpos : h-2-1 = h-3 := by omega
    simp [run,next,c1,hBread,hpos]
  have hleftTape (x : Int) (hx : x ≤ h-3) : c1.tape x = t x := by
    have hne1 : x ≠ h-1 := by omega
    have hne2 : x ≠ h-2 := by omega
    have hout := shuttleFill_outside t h x (2*n+2) (Or.inl (by omega))
    change setBit (setBit (shuttleFill t h (2*n+2)) (h-1) true)
      (h-2) true x = t x
    simp [setBit,hne1,hne2,hout]
  have hfb' : fbExtended m c1 := by
    constructor
    · rfl
    · intro i hi
      constructor
      · change c1.tape (h-3-2*(i:Int)) = false
        rw [hleftTape (h-3-2*(i:Int)) (by omega)]
        exact (hfb i hi).1
      · have hpos : c1.h-2*(i:Int)-1 = h-4-2*(i:Int) := by simp [c1]; omega
        change c1.tape (c1.h-2*(i:Int)-1) = true
        rw [hpos,hleftTape (h-4-2*(i:Int)) (by omega)]
        exact (hfb i hi).2
  have hfbRun : run (2*m) c1 = some (fbMany m c1) := fb_two_n m c1 hfb'
  have hnotF : ¬ fbTouched m c1 (h-3-2*(m:Int)) := by
    intro hx
    rcases hx with ⟨i,hi,heq⟩
    change h-3-2*(m:Int) = (h-3)-2*(i:Int) at heq
    omega
  have hnotB : ¬ fbTouched m c1 (h-4-2*(m:Int)) := by
    intro hx
    rcases hx with ⟨i,hi,heq⟩
    change h-4-2*(m:Int) = (h-3)-2*(i:Int) at heq
    omega
  have hFread : (fbMany m c1).tape (h-3-2*(m:Int)) = false := by
    rw [fb_many_unvisited m c1 _ hnotF]
    rw [hleftTape (h-3-2*(m:Int)) (by omega)]
    exact hfinalF
  have hBread : (fbMany m c1).tape (h-4-2*(m:Int)) = false := by
    rw [fb_many_unvisited m c1 _ hnotB]
    rw [hleftTape (h-4-2*(m:Int)) (by omega)]
    exact hfinalB
  have hlast : run 1 (fbMany m c1) =
      some ⟨.B,h-4-2*(m:Int),
        setBit (fbMany m c1).tape (h-3-2*(m:Int)) true⟩ := by
    have hhead' : (fbMany m c1).h = h-3-2*(m:Int) := by
      simpa [c1] using fbMany_head m c1
    have hhead'' : (fbMany m c1).h = h-(3+2*(m:Int)) := by
      have hidx : h-3-2*(m:Int) = h-(3+2*(m:Int)) := by omega
      rw [hhead',hidx]
    have hq' : (fbMany m c1).q = .F := fbMany_state m c1 rfl
    have hFread'' : (fbMany m c1).tape (h-(3+2*(m:Int))) = false := by
      have hidx : h-(3+2*(m:Int)) = h-3-2*(m:Int) := by omega
      rw [hidx]
      exact hFread
    have hpos'' : h-(3+2*(m:Int))-1 = h-4-2*(m:Int) := by omega
    simp [run,next,hq',hFread'',hhead'',hpos'']
  have hrest : run (1+(1+(2*m+1)))
      (⟨.F,h-1,shuttleFill t h (2*n+2)⟩ : Conf) =
      some ⟨.B,h-4-2*(m:Int),
        setBit (fbMany m c1).tape (h-3-2*(m:Int)) true⟩ := by
    have hd1 := run_add 1 (1+(2*m+1))
      (⟨.F,h-1,shuttleFill t h (2*n+2)⟩ : Conf)
    rw [hd1,hFstep]
    simp only [Option.bind_some]
    have hd2 := run_add 1 (2*m+1)
      (⟨.B,h-2,setBit (shuttleFill t h (2*n+2)) (h-1) true⟩ : Conf)
    rw [hd2,hBstep]
    simp only [Option.bind_some]
    have hd3 := run_add (2*m) 1 c1
    rw [hd3,hfbRun]
    simp only [Option.bind_some]
    exact hlast
  have htotal : 4*n+2*m+6 = (4*n+3)+(1+(1+(2*m+1))) := by omega
  have hd := run_add (4*n+3) (1+(1+(2*m+1))) (⟨.D,h,t⟩ : Conf)
  rw [htotal,hd,hsh']
  simp only [Option.bind_some]
  constructor
  · exact hrest
  · change (setBit (fbMany m c1).tape (h-3-2*(m:Int)) true)
      (h-4-2*(m:Int)) = false
    have hne : h-4-2*(m:Int) ≠ h-3-2*(m:Int) := by omega
    have hBread' : (fbMany m c1).tape (h-(4+2*(m:Int))) = false := by
      have hidx : h-(4+2*(m:Int)) = h-4-2*(m:Int) := by omega
      rw [hidx]
      exact hBread
    simp [setBit,hne,hBread']

def b0C0DTape (b : Conf) : Int → Bool :=
  setBit (setBit b.tape b.h true) (b.h-1) true

def dRetreatResult (n m : Nat) (t : Int → Bool) (h : Int) : Conf :=
  ⟨.B,h-4-2*(m:Int),
    setBit (fbMany m
      (⟨.F,h-3,
        setBit (setBit (shuttleFill t h (2*n+2)) (h-1) true)
          (h-2) true⟩ : Conf)).tape
      (h-3-2*(m:Int)) true⟩

/-- The immediate B/0-C/0-D/1 prefix, followed by an odd D shuttle and
    any finite alternating F/0-B/1 retreat, returns to B/0. -/
theorem b0_c0_d1_odd_retreat_to_b0 (b : Conf) (n m : Nat)
    (hb : Reach b) (hb0 : BZero b)
    (hCzero : b.tape (b.h-1) = false)
    (hones : ∀ j : Nat, j < 2*n+1 →
      b0C0DTape b (b.h-2+(j:Int)) = true)
    (hzero : b0C0DTape b (b.h-2+(2*n+1:Int)) = false)
    (hleftF : b0C0DTape b (b.h-3) = false)
    (hleftB : b0C0DTape b (b.h-4) = true)
    (hfb : ∀ i : Nat, i < m →
      b0C0DTape b (b.h-5-2*(i:Int)) = false ∧
      b0C0DTape b (b.h-6-2*(i:Int)) = true)
    (hfinalF : b0C0DTape b (b.h-5-2*(m:Int)) = false)
    (hfinalB : b0C0DTape b (b.h-6-2*(m:Int)) = false) :
    ∃ b', Reach b' ∧ BZero b' := by
  rcases b with ⟨q,pos,t⟩
  rcases hb0 with ⟨hq,hB0⟩
  change q = .B at hq
  subst q
  let b0 : Conf := ⟨.B,pos,t⟩
  let c : Conf := ⟨.C,pos-1,setBit t pos true⟩
  have hB0' : t pos = false := by simpa [b0] using hB0
  have hCzero' : t (pos-1) = false := by simpa [b0] using hCzero
  have hb' : Reach b0 := by simpa [b0] using hb
  have hbstep : next b0 = some c := by simp [next,b0,c,hB0']
  have hcReach : Reach c := Reach.follow hb' hbstep
  have hreadC : (setBit t pos true) (pos-1) = false := by
    have hne : pos-1 ≠ pos := by omega
    simp [setBit,hne,hCzero']
  let tD : Int → Bool := setBit (setBit t pos true) (pos-1) true
  let d : Conf := ⟨.D,pos-2,tD⟩
  have hcstep : next c = some d := by
    have hpos : pos-1-1 = pos-2 := by omega
    simp [next,c,d,tD,hreadC,hpos]
  have hdReach : Reach d := Reach.follow hcReach hcstep
  have hones' : ∀ j : Nat, j < 2*n+1 → tD (pos-2+(j:Int)) = true := by
    simpa [tD,b0,b0C0DTape] using hones
  have hzero' : tD (pos-2+(2*n+1:Int)) = false := by
    simpa [tD,b0,b0C0DTape] using hzero
  have hleftF' : tD ((pos-2)-1) = false := by
    simpa [tD,b0,b0C0DTape,show pos-2-1=pos-3 by omega] using hleftF
  have hleftB' : tD ((pos-2)-2) = true := by
    simpa [tD,b0,b0C0DTape,show pos-2-2=pos-4 by omega] using hleftB
  have hfb' : ∀ i : Nat, i < m →
      tD ((pos-2)-3-2*(i:Int)) = false ∧
      tD ((pos-2)-4-2*(i:Int)) = true := by
    intro i hi
    simpa [tD,b0,b0C0DTape,
      show pos-2-3-2*(i:Int)=pos-5-2*(i:Int) by omega,
      show pos-2-4-2*(i:Int)=pos-6-2*(i:Int) by omega] using hfb i hi
  have hfinalF' : tD ((pos-2)-3-2*(m:Int)) = false := by
    simpa [tD,b0,b0C0DTape,show pos-2-3-2*(m:Int)=pos-5-2*(m:Int) by omega] using hfinalF
  have hfinalB' : tD ((pos-2)-4-2*(m:Int)) = false := by
    simpa [tD,b0,b0C0DTape,show pos-2-4-2*(m:Int)=pos-6-2*(m:Int) by omega] using hfinalB
  have hret := d1_retreat_to_b0 n m tD (pos-2)
    hones' hzero' hleftF' hleftB' hfb' hfinalF' hfinalB'
  let bout : Conf := dRetreatResult n m tD (pos-2)
  have hbout : BZero bout := by
    refine ⟨rfl,?_⟩
    simpa [bout,dRetreatResult,tD] using hret.2
  have hboutReach : Reach bout := by
    apply reachable_of_run (4*n+2*m+6) d bout hdReach
    simpa [bout,dRetreatResult,tD] using hret.1
  exact ⟨bout,hboutReach,hbout⟩

/-- A B/0 whose leftward C scan reaches the D/0-E/1-A/0 branch
    enters an odd F/1 wave, then returns to a reached B/0 after any
    finite alternating B/1-F/0 retreat. -/
theorem b0_cphase_d0_odd_wave_return (b : Conf) (r m : Nat)
    (hb : Reach b) (hb0 : BZero b)
    (hscan : ∀ i : Nat, i < r → b.tape (b.h-1-(i:Int)) = true)
    (hzeroC : b.tape (b.h-1-(r:Int)) = false)
    (hDzero : b.tape (b.h-2-(r:Int)) = false)
    (hEone : b.tape (b.h-3-(r:Int)) = true)
    (hAzero : b.tape (b.h-4-(r:Int)) = false)
    (hLeft1 : b.tape (b.h-5-(r:Int)) = true)
    (hfb : ∀ i : Nat, i < m →
      b.tape (b.h-6-(r:Int)-2*(i:Int)) = false ∧
      b.tape (b.h-7-(r:Int)-2*(i:Int)) = true)
    (hfinalF : b.tape (b.h-6-(r:Int)-2*(m:Int)) = false)
    (hfinalB : b.tape (b.h-7-(r:Int)-2*(m:Int)) = false) :
    ∃ b', Reach b' ∧ BZero b' := by
  obtain ⟨c,hc,hphase⟩ := scan_from_B b hb hb0 r hscan
  obtain ⟨_,hC,hpos,hprefix,_⟩ := hphase
  have hCzero : c.tape c.h = false := by
    calc
      c.tape c.h = b.tape c.h := hprefix c.h (by omega)
      _ = b.tape (b.h-1-(r:Int)) := by rw [hpos]
      _ = false := hzeroC
  have hDzeroC : c.tape (c.h-1) = false := by
    calc
      c.tape (c.h-1) = b.tape (c.h-1) := hprefix (c.h-1) (by omega)
      _ = b.tape (b.h-2-(r:Int)) := by rw [hpos]; congr 1 <;> omega
      _ = false := hDzero
  have hEoneC : c.tape (c.h-2) = true := by
    calc
      c.tape (c.h-2) = b.tape (c.h-2) := hprefix (c.h-2) (by omega)
      _ = b.tape (b.h-3-(r:Int)) := by rw [hpos]; congr 1 <;> omega
      _ = true := hEone
  have hAzeroC : c.tape (c.h-3) = false := by
    calc
      c.tape (c.h-3) = b.tape (c.h-3) := hprefix (c.h-3) (by omega)
      _ = b.tape (b.h-4-(r:Int)) := by rw [hpos]; congr 1 <;> omega
      _ = false := hAzero
  let d : Conf := ⟨.D,c.h-1,setBit c.tape c.h true⟩
  have hcstep : next c = some d := by simp [next,hC,hCzero,d]
  have hreadD : (setBit c.tape c.h true) (c.h-1) = false := by
    simp [setBit,show c.h-1 ≠ c.h by omega,hDzeroC]
  let e : Conf := ⟨.E,c.h-2,setBit d.tape (c.h-1) false⟩
  have hdstep : next d = some e := by
    have hpos : c.h-1-1 = c.h-2 := by omega
    simp [next,d,e,hreadD,hpos]
  have hreadE : (setBit d.tape (c.h-1) false) (c.h-2) = true := by
    have hne : c.h-2 ≠ c.h-1 := by omega
    have hne' : c.h-2 ≠ c.h := by omega
    simp [setBit,hne,d,setBit,hne',hEoneC]
  let a : Conf := ⟨.A,c.h-3,setBit e.tape (c.h-2) true⟩
  have hestep : next e = some a := by
    have hpos : c.h-2-1 = c.h-3 := by omega
    simp [next,e,a,hreadE,hpos]
  have hreadA : (setBit e.tape (c.h-2) true) (c.h-3) = false := by
    have hne : c.h-3 ≠ c.h-2 := by omega
    have hne1 : c.h-3 ≠ c.h-1 := by omega
    have hne2 : c.h-3 ≠ c.h := by omega
    simp [setBit,hne,e,setBit,hne1,d,setBit,hne2,hAzeroC]
  let b1 : Conf := ⟨.B,c.h-2,setBit a.tape (c.h-3) true⟩
  have hastep : next a = some b1 := by
    have hpos : c.h-3+1 = c.h-2 := by omega
    simp [next,a,b1,hreadA,hpos]
  have hreadB : (setBit a.tape (c.h-3) true) (c.h-2) = true := by
    have hne : c.h-2 ≠ c.h-3 := by omega
    simp [setBit,hne,a,setBit]
  let f : Conf := ⟨.F,c.h-3,setBit b1.tape (c.h-2) true⟩
  have hb1step : next b1 = some f := by
    have hpos : c.h-2-1 = c.h-3 := by omega
    simp [next,b1,f,hreadB,hpos]
  have hfReach : Reach f := Reach.follow (Reach.follow (Reach.follow
      (Reach.follow (Reach.follow hc hcstep) hdstep) hestep) hastep) hb1step
  have hfhead : f.tape (c.h-3) = true := by
    change setBit b1.tape (c.h-2) true (c.h-3) = true
    simp [setBit,b1]
  have hfright : f.tape (c.h-2) = true := by
    change setBit b1.tape (c.h-2) true (c.h-2) = true
    simp [setBit]
  have hfsentinel : f.tape (c.h-1) = false := by
    change setBit b1.tape (c.h-2) true (c.h-1) = false
    have hne : c.h-1 ≠ c.h-2 := by omega
    simp [setBit,hne,b1,a,e]
  have hfleft (x : Int) (hx : x ≤ c.h-4) : f.tape x = b.tape x := by
    have hne0 : x ≠ c.h := by omega
    have hne1 : x ≠ c.h-1 := by omega
    have hne2 : x ≠ c.h-2 := by omega
    have hne3 : x ≠ c.h-3 := by omega
    have hcp : c.tape x = b.tape x := hprefix x (by omega)
    change setBit b1.tape (c.h-2) true x = b.tape x
    simp [setBit,hne2,b1,a,e,d,setBit,hne0,hne1,hne3,hcp]
  have hfleft1 : f.tape (c.h-4) = true := by
    rw [hfleft (c.h-4) (by omega)]
    have heq : c.h-4 = b.h-5-(r:Int) := by rw [hpos]; omega
    rw [heq]
    exact hLeft1
  have hfback : ∀ i : Nat, i < m →
      f.tape (c.h-5-2*(i:Int)) = false ∧
      f.tape (c.h-6-2*(i:Int)) = true := by
    intro i hi
    constructor
    · rw [hfleft (c.h-5-2*(i:Int)) (by omega)]
      have heq : c.h-5-2*(i:Int) = b.h-6-(r:Int)-2*(i:Int) := by rw [hpos]; omega
      rw [heq]
      exact (hfb i hi).1
    · rw [hfleft (c.h-6-2*(i:Int)) (by omega)]
      have heq : c.h-6-2*(i:Int) = b.h-7-(r:Int)-2*(i:Int) := by rw [hpos]; omega
      rw [heq]
      exact (hfb i hi).2
  have hffinal : f.tape (c.h-5-2*(m:Int)) = false := by
    rw [hfleft (c.h-5-2*(m:Int)) (by omega)]
    have heq : c.h-5-2*(m:Int) = b.h-6-(r:Int)-2*(m:Int) := by rw [hpos]; omega
    rw [heq]
    exact hfinalF
  have hbfinal : f.tape (c.h-6-2*(m:Int)) = false := by
    rw [hfleft (c.h-6-2*(m:Int)) (by omega)]
    have heq : c.h-6-2*(m:Int) = b.h-7-(r:Int)-2*(m:Int) := by rw [hpos]; omega
    rw [heq]
    exact hfinalB
  have hret := odd_f1_retreat_to_b0 0 m f.tape (c.h-3)
    hfhead (by
      intro j hj
      have hj0 : j = 0 := by omega
      subst j
      simpa [show c.h-3+1 = c.h-2 by omega] using hfright)
    (by simpa [show c.h-3+2 = c.h-1 by omega] using hfsentinel)
    (by simpa [show c.h-3-1 = c.h-4 by omega] using hfleft1)
    (by
      intro i hi
      constructor
      · simpa [show c.h-3-2-2*(i:Int) = c.h-5-2*(i:Int) by omega] using (hfback i hi).1
      · simpa [show c.h-3-3-2*(i:Int) = c.h-6-2*(i:Int) by omega] using (hfback i hi).2)
    (by simpa [show c.h-3-2-2*(m:Int) = c.h-5-2*(m:Int) by omega] using hffinal)
    (by simpa [show c.h-3-3-2*(m:Int) = c.h-6-2*(m:Int) by omega] using hbfinal)
  let bout : Conf := oddRetreatResult 0 m f.tape (c.h-3)
  have hbout : BZero bout := by
    refine ⟨rfl,?_⟩
    simpa [bout,oddRetreatResult] using hret.2
  have hboutReach : Reach bout := by
    apply reachable_of_run (2*m+7) f bout hfReach
    simpa [bout,oddRetreatResult] using hret.1
  exact ⟨bout,hboutReach,hbout⟩

#print axioms BB6Root119.odd_f1_retreat_to_b0
#print axioms BB6Root119.odd_f1_two_wave_chain_to_b0
#print axioms BB6Root119.d1_retreat_to_b0
#print axioms BB6Root119.b0_c0_d1_odd_retreat_to_b0
#print axioms BB6Root119.b0_cphase_d0_odd_wave_return
end BB6Root119
