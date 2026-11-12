import Root119EvenExtra
import Root119CPhaseReturn
import Root119CGate

namespace BB6Root119

/-- A run of successful shuttle steps preserves reachability from blank. -/
theorem shuttleRun_reach {n : Nat} {c d : Conf}
    (hc : Reach c) (hrun : shuttleRun n c = some d) : Reach d := by
  induction n generalizing c with
  | zero =>
      simp [shuttleRun] at hrun
      cases hrun
      exact hc
  | succ n ih =>
      simp only [shuttleRun] at hrun
      cases hstep : next c with
      | none =>
          simp [hstep] at hrun
      | some c' =>
          simp [hstep] at hrun
          exact ih (Reach.follow hc hstep) hrun

/-- The even sweep leaves every cell strictly before its starting point alone. -/
theorem evenSweepTape_before (n : Nat) (t : Int → Bool) (h x : Int)
    (hx : x < h) : evenSweepTape n t h x = t x := by
  induction n generalizing t h x with
  | zero =>
      rfl
  | succ n ih =>
      change evenSweepTape n
        (setBit (setBit t h true) (h+1) false) (h+2) x = t x
      have hrec := ih (setBit (setBit t h true) (h+1) false) (h+2) x
        (by omega)
      rw [hrec]
      simp [setBit, show x ≠ h by omega, show x ≠ h+1 by omega]

/-- Even-indexed cells in the swept prefix are set to one. -/
theorem evenSweepTape_even (n : Nat) (t : Int → Bool) (h : Int)
    (j : Nat) (hj : j < n) :
    evenSweepTape n t h (h + 2*(j:Int)) = true := by
  induction n generalizing t h j with
  | zero =>
      omega
  | succ n ih =>
      by_cases hj0 : j = 0
      · subst j
        change evenSweepTape n
          (setBit (setBit t h true) (h+1) false) (h+2) h = true
        have hbefore := evenSweepTape_before n
          (setBit (setBit t h true) (h+1) false) (h+2) h (by omega)
        rw [hbefore]
        simp [setBit]
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
        have hj' : j-1 < n := by omega
        have heq : h + 2*(j:Int) = (h+2) + 2*((j-1):Int) := by omega
        change evenSweepTape n
          (setBit (setBit t h true) (h+1) false) (h+2)
          (h + 2*(j:Int)) = true
        rw [heq]
        exact ih (setBit (setBit t h true) (h+1) false) (h+2) (j-1) hj'

/-- Odd-indexed cells in the swept prefix are set to zero. -/
theorem evenSweepTape_odd (n : Nat) (t : Int → Bool) (h : Int)
    (j : Nat) (hj : j < n) :
    evenSweepTape n t h (h + 2*(j:Int) + 1) = false := by
  induction n generalizing t h j with
  | zero =>
      omega
  | succ n ih =>
      by_cases hj0 : j = 0
      · subst j
        change evenSweepTape n
          (setBit (setBit t h true) (h+1) false) (h+2) (h+1) = false
        have hbefore := evenSweepTape_before n
          (setBit (setBit t h true) (h+1) false) (h+2) (h+1) (by omega)
        rw [hbefore]
        simp [setBit]
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
        have hj' : j-1 < n := by omega
        have heq : h + 2*(j:Int) + 1 =
            (h+2) + 2*((j-1):Int) + 1 := by omega
        change evenSweepTape n
          (setBit (setBit t h true) (h+1) false) (h+2)
          (h + 2*(j:Int) + 1) = false
        rw [heq]
        exact ih (setBit (setBit t h true) (h+1) false) (h+2) (j-1) hj'

/-- Tape after the terminal D0,E0,A0 triple of an even sweep. -/
def evenSweepBResultTape (n : Nat) (t : Int → Bool) (h : Int) :
    Int → Bool :=
  let p := h + 2*(n+1)
  setBit (setBit (setBit (evenSweepTape (n+1) t h) p false)
    (p-1) true) p true

/-- The even-sweep B result is one at its two final written cells. -/
theorem evenSweepBResultTape_at_p (n : Nat) (t : Int → Bool) (h : Int) :
    evenSweepBResultTape n t h (h+2*(n+1)) = true := by
  simp [evenSweepBResultTape, setBit]

theorem evenSweepBResultTape_at_p_sub_one
    (n : Nat) (t : Int → Bool) (h : Int) :
    evenSweepBResultTape n t h (h+2*(n+1)-1) = true := by
  have hne : h+2*(n+1)-1 ≠ h+2*(n+1) := by omega
  simp [evenSweepBResultTape, setBit, hne]

/-- The even-sweep B result agrees with the sweep below its final two writes. -/
theorem evenSweepBResultTape_before
    (n : Nat) (t : Int → Bool) (h x : Int)
    (hx : x ≤ h+2*(n+1)-2) :
    evenSweepBResultTape n t h x = evenSweepTape (n+1) t h x := by
  have hne0 : x ≠ h+2*(n+1) := by omega
  have hne1 : x ≠ h+2*(n+1)-1 := by omega
  simp [evenSweepBResultTape, setBit, hne0, hne1]

/-- Beyond the even sweep, the B result agrees with the original tape. -/
theorem evenSweepBResultTape_after
    (n : Nat) (t : Int → Bool) (h x : Int)
    (hx : h+2*(n+1)+1 ≤ x) :
    evenSweepBResultTape n t h x = t x := by
  have hne0 : x ≠ h+2*(n+1) := by omega
  have hne1 : x ≠ h+2*(n+1)-1 := by omega
  have hright := evenSweepTape_right (n+1) t h x (by omega)
  simp [evenSweepBResultTape, setBit, hne0, hne1, hright]

/-- Exact source-level D even sweep followed by its D0,E0,A0 tail. -/
theorem evenSweep_to_B_conf (n : Nat) (t : Int → Bool) (h : Int)
    (ones : ∀ j : Nat, j < 2*(n+1) → t (h+(j:Int)) = true)
    (zero : t (h+(2*(n+1):Int)) = false) :
    shuttleRun (2*(n+1)+3) ⟨.D,h,t⟩ =
      some ⟨.B,h+2*(n+1)+1,evenSweepBResultTape n t h⟩ := by
  let p : Int := h+2*(n+1)
  let v := evenSweepTape (n+1) t h
  let v1 := setBit v p false
  let v2 := setBit v1 (p-1) true
  let v3 := setBit v2 p true
  have ds := evenSweep (n+1) t h ones
  have hz : v p = false := by
    have hh := evenSweepTape_right (n+1) t h p (by dsimp [p]; omega)
    dsimp [p,v] at hh ⊢
    exact hh.trans zero
  have hl : v (p-1) = false := by
    dsimp [p,v]
    exact evenSweepTape_last n t h
  have hleft : v1 (p-1) = false := by
    have hne : p-1 ≠ p := by omega
    simp [v1,setBit,hne,hl]
  have hright : v2 p = false := by
    have hne : p ≠ p-1 := by omega
    simp [v2,setBit,hne,v1,hz]
  have hs1 : next ⟨Q.D,p,v⟩ = some ⟨Q.E,p-1,v1⟩ := by
    simp [next,hz,v1]
  have hs2 : next ⟨Q.E,p-1,v1⟩ = some ⟨Q.A,p,v2⟩ := by
    simp [next,hleft,v2]
  have hs3 : next ⟨Q.A,p,v2⟩ = some ⟨Q.B,p+1,v3⟩ := by
    simp [next,hright,v3]
  have ht : shuttleRun 3 ⟨Q.D,p,v⟩ = some ⟨Q.B,p+1,v3⟩ := by
    simp [shuttleRun,hs1,hs2,hs3]
  calc
    shuttleRun (2*(n+1)+3) ⟨.D,h,t⟩ =
        (shuttleRun (2*(n+1)) ⟨.D,h,t⟩).bind (shuttleRun 3) := by
          rw [shuttleRun_add]
    _ = shuttleRun 3 ⟨.D,p,v⟩ := by
          simpa [p,v] using
            congrArg (fun o => o.bind (shuttleRun 3)) ds
    _ = some ⟨.B,p+1,v3⟩ := ht
    _ = some ⟨.B,h+2*(n+1)+1,evenSweepBResultTape n t h⟩ := by
          simp [p,v,v1,v2,v3,evenSweepBResultTape]

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
    Unlike the shielded version, this is valid with a 1100 marker behind it. -/
theorem cphase_d1_tail_raw (c : Conf)
    (hC : c.q = .C)
    (hCzero : c.tape c.h = false)
    (hDone : c.tape (c.h-1) = true)
    (hzero1 : c.tape (c.h+1) = false)
    (hzero2 : c.tape (c.h+2) = false) :
    ∃ bout, shuttleRun 6 c = some bout ∧
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
  have hdread : d.tape d.h = true := by
    simp [d,setBit,show c.h-1 ≠ c.h by omega,hDone]
  have hfread : f.tape f.h = true := by
    simp [f,d,setBit]
  have hd2read : d2.tape d2.h = false := by
    simp [d2,f,d,setBit,hzero1]
  have heread : e.tape e.h = false := by
    simp [e,d2,f,d,setBit]
  have haread : a.tape a.h = false := by
    simp [a,e,d2,f,d,setBit]
  have hs1 : next c = some d := by
    simp [next,hC,hCzero,d]
  have hs2 : next d = some f := by
    simp [next,d,hdread,f]
  have hs3 : next f = some d2 := by
    simp [next,f,hfread,d2]
  have hs4 : next d2 = some e := by
    simp [next,d2,hd2read,e]
  have hs5 : next e = some a := by
    simp [next,e,heread,a]
  have hs6 : next a = some bout := by
    simp [next,a,haread,bout]
  have hrun : shuttleRun 6 c = some bout := by
    simp [shuttleRun,hs1,hs2,hs3,hs4,hs5,hs6]
  have hBzero : BZero bout := by
    constructor
    · rfl
    · simp [bout,a,e,d2,f,d,setBit,hzero2]
  have hleft : bout.tape (c.h-1) = true := by
    simp [bout,a,e,d2,f,d,setBit]
  have hcenter : bout.tape c.h = true := by
    simp [bout,a,e,d2,f,d,setBit]
  have hright : bout.tape (c.h+1) = true := by
    simp [bout,a,e,d2,f,d,setBit]
  have hpres : ∀ x : Int, x ≤ c.h-2 → bout.tape x = c.tape x := by
    intro x hx
    simp [bout,a,e,d2,f,d,setBit,
      show x ≠ c.h-1 by omega,
      show x ≠ c.h by omega,
      show x ≠ c.h+1 by omega]
  exact ⟨bout,hrun,hBzero,rfl,hleft,hcenter,hright,hpres⟩

/-- The finite alternating B0 ladder necessarily reaches the C/0 110 gate. -/
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
          have hx : b.h-1-(1:Int) = b.h-2 := by omega
          rw [hx]
          exact hp.left2
        · subst i
          have hx : b.h-1-(2:Int) = b.h-3 := by omega
          rw [hx]
          exact hp.left3
      obtain ⟨c,hrun,hc,hphase,hzeros⟩ :=
        scan_from_B_exact b hb hp.hB 3 hscan
      rcases hphase with ⟨_,hC,hpos,hpres,_⟩
      have hpos' : c.h = b.h-4 := by omega
      have hCG : CGate c := by
        refine ⟨hC, ?_, ?_, ?_, ?_⟩
        · calc
            c.tape c.h = b.tape c.h := hpres c.h (by omega)
            _ = b.tape (b.h-4) := by rw [hpos']
            _ = false := hp.final0
        · have hx : c.h-1 = b.h-5 := by rw [hpos']; omega
          calc
            c.tape (c.h-1) = b.tape (c.h-1) := hpres (c.h-1) (by omega)
            _ = b.tape (b.h-5) := by rw [hx]
            _ = false := hp.final00
        · have hx : c.h-2 = b.h-6 := by rw [hpos']; omega
          calc
            c.tape (c.h-2) = b.tape (c.h-2) := hpres (c.h-2) (by omega)
            _ = b.tape (b.h-6) := by rw [hx]
            _ = true := hp.final1
        · have hx : c.h-3 = b.h-7 := by rw [hpos']; omega
          calc
            c.tape (c.h-3) = b.tape (c.h-3) := hpres (c.h-3) (by omega)
            _ = b.tape (b.h-7) := by rw [hx]
            _ = true := hp.final11
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
          have hx : b.h-1-(1:Int) = b.h-2 := by omega
          rw [hx]
          exact hp.left2
        · subst i
          have hx : b.h-1-(2:Int) = b.h-3 := by omega
          rw [hx]
          exact hp.left3
      obtain ⟨c,hrun,hc,hphase,hzeros⟩ :=
        scan_from_B_exact b hb hp.hB 3 hscan
      rcases hphase with ⟨_,hC,hpos,hpres,_⟩
      have hpos' : c.h = b.h-4 := by omega
      have hzero0 : b.tape (b.h-4) = false := (hp.alternating 0 (by omega)).1
      have hdone0 : b.tape (b.h-5) = true := (hp.alternating 0 (by omega)).2
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
      obtain ⟨b',hret,hB',hh',hleft,hcenter,hright,hpres2⟩ :=
        cphase_d1_tail_raw c hC hczero hdone hzero1 hzero2
      have hb' : Reach b' := shuttleRun_reach hc hret
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

/-- F/1 with left suffix 110, an even positive right 1-run, and two
    following zeros reaches the fatal C/0 110 gate. -/
structure F1EvenMarker (n : Nat) (c : Conf) : Prop where
  state : c.q = .F
  head : c.tape c.h = true
  left0 : c.tape (c.h-1) = false
  left1 : c.tape (c.h-2) = true
  left2 : c.tape (c.h-3) = true
  rightOnes : ∀ j : Nat, j < 2*(n+1) →
    c.tape (c.h+1+(j:Int)) = true
  rightZero : c.tape (c.h+1+(2*(n+1):Int)) = false
  afterZero : c.tape (c.h+2*(n+1)+2) = false

/-- An even F1 marker wave followed by two zeros reaches a C gate.
    This is a conditional halting certificate, not a claim that the
    corresponding F1 state is reachable in the blank run. -/
theorem f1_even_marker_to_CGate (n : Nat) (c : Conf)
    (hc : Reach c) (hp : F1EvenMarker n c) :
    ∃ cg, Reach cg ∧ CGate cg := by
  let t1 := setBit c.tape c.h false
  let d : Conf := ⟨.D,c.h+1,t1⟩
  have hstep : next c = some d := by
    simp [next,d,t1,hp.state,hp.head]
  have hones : ∀ j : Nat, j < 2*(n+1) →
      t1 (c.h+1+(j:Int)) = true := by
    intro j hj
    have hne : c.h+1+(j:Int) ≠ c.h := by omega
    simpa [t1,setBit,hne] using hp.rightOnes j hj
  have hzero : t1 (c.h+1+(2*(n+1):Int)) = false := by
    have hne : c.h+1+(2*(n+1):Int) ≠ c.h := by omega
    simpa [t1,setBit,hne] using hp.rightZero
  let b : Conf := ⟨.B,c.h+2*(n+1)+2,
    evenSweepBResultTape n t1 (c.h+1)⟩
  have hD : shuttleRun (2*(n+1)+3) d = some b := by
    simpa [d,b] using
      (evenSweep_to_B_conf n t1 (c.h+1) hones hzero)
  have hrun : shuttleRun (1+(2*(n+1)+3)) c = some b := by
    rw [shuttleRun_add]
    simp [shuttleRun,hstep,hD]
  have hb : Reach b := shuttleRun_reach hc hrun
  have hpat : MarkerB0Pattern n b := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · constructor
      · rfl
      · have hafter := evenSweepBResultTape_after n t1 (c.h+1) b.h (by
          dsimp [b]
          omega)
        calc
          b.tape b.h = t1 b.h := by simpa [b] using hafter
          _ = c.tape b.h := by
            simp [t1,setBit,show b.h ≠ c.h by dsimp [b]; omega]
          _ = false := by
            dsimp [b]
            exact hp.afterZero
    · have hpbit := evenSweepBResultTape_at_p n t1 (c.h+1)
      simpa [b] using hpbit
    · have hpbit := evenSweepBResultTape_at_p_sub_one n t1 (c.h+1)
      simpa [b] using hpbit
    · have hbefore := evenSweepBResultTape_before n t1 (c.h+1)
        (b.h-3) (by dsimp [b]; omega)
      have heven := evenSweepTape_even (n+1) t1 (c.h+1) n (by omega)
      have hidx : b.h-3 = (c.h+1)+2*(n:Int) := by dsimp [b]; omega
      rw [hidx] at hbefore ⊢
      rw [hbefore]
      exact heven
    · intro i hi
      constructor
      · have hbefore := evenSweepBResultTape_before n t1 (c.h+1)
          (b.h-4-2*(i:Int)) (by dsimp [b]; omega)
        have hodd := evenSweepTape_odd (n+1) t1 (c.h+1) (n-i-1) (by omega)
        have hidx : b.h-4-2*(i:Int) =
            (c.h+1)+2*((n-i-1):Int)+1 := by dsimp [b]; omega
        rw [hidx] at hbefore ⊢
        rw [hbefore]
        exact hodd
      · have hbefore := evenSweepBResultTape_before n t1 (c.h+1)
          (b.h-5-2*(i:Int)) (by dsimp [b]; omega)
        have heven := evenSweepTape_even (n+1) t1 (c.h+1) (n-i-1) (by omega)
        have hidx : b.h-5-2*(i:Int) =
            (c.h+1)+2*((n-i-1):Int) := by dsimp [b]; omega
        rw [hidx] at hbefore ⊢
        rw [hbefore]
        exact heven
    · have hbefore := evenSweepBResultTape_before n t1 (c.h+1)
        (b.h-4-2*(n:Int)) (by dsimp [b]; omega)
      have hidx : b.h-4-2*(n:Int) = c.h := by dsimp [b]; omega
      rw [hidx] at hbefore ⊢
      rw [hbefore]
      have hpre := evenSweepTape_before (n+1) t1 (c.h+1) c.h (by omega)
      rw [hpre]
      simp [t1,setBit]
    · have hbefore := evenSweepBResultTape_before n t1 (c.h+1)
        (b.h-5-2*(n:Int)) (by dsimp [b]; omega)
      have hidx : b.h-5-2*(n:Int) = c.h-1 := by dsimp [b]; omega
      rw [hidx] at hbefore ⊢
      rw [hbefore]
      have hpre := evenSweepTape_before (n+1) t1 (c.h+1) (c.h-1) (by omega)
      rw [hpre]
      simpa [t1,setBit] using hp.left0
    · have hbefore := evenSweepBResultTape_before n t1 (c.h+1)
        (b.h-6-2*(n:Int)) (by dsimp [b]; omega)
      have hidx : b.h-6-2*(n:Int) = c.h-2 := by dsimp [b]; omega
      rw [hidx] at hbefore ⊢
      rw [hbefore]
      have hpre := evenSweepTape_before (n+1) t1 (c.h+1) (c.h-2) (by omega)
      rw [hpre]
      simpa [t1,setBit] using hp.left1
    · have hbefore := evenSweepBResultTape_before n t1 (c.h+1)
        (b.h-7-2*(n:Int)) (by dsimp [b]; omega)
      have hidx : b.h-7-2*(n:Int) = c.h-3 := by dsimp [b]; omega
      rw [hidx] at hbefore ⊢
      rw [hbefore]
      have hpre := evenSweepTape_before (n+1) t1 (c.h+1) (c.h-3) (by omega)
      rw [hpre]
      simpa [t1,setBit] using hp.left2
  exact markerB0Pattern_to_CGate n b hb hpat

#print axioms BB6Root119.f1_even_marker_to_CGate
#print axioms BB6Root119.markerB0Pattern_to_CGate

end BB6Root119
