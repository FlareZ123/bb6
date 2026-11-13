import Root119EvenExtra

namespace BB6Root119

/-- The eight-step B/0 prefix when the three cells immediately to the left
    are zero. It ends at F/1 on the original B head. -/
def zeroLeftPrefixTape (t : Int → Bool) (h : Int) : Int → Bool :=
  setBit (setBit (setBit (setBit t h true) (h-1) true) (h-2) false)
    (h-3) true

theorem zeroLeftPrefixTape_head (t : Int → Bool) (h : Int) :
    zeroLeftPrefixTape t h h = true := by
  have h1 : h ≠ h-1 := by omega
  have h2 : h ≠ h-2 := by omega
  have h3 : h ≠ h-3 := by omega
  simp [zeroLeftPrefixTape, setBit, h1, h2, h3]

theorem zeroLeftPrefixTape_right (t : Int → Bool) (h x : Int)
    (hx : h < x) : zeroLeftPrefixTape t h x = t x := by
  have h0 : x ≠ h := by omega
  have h1 : x ≠ h-1 := by omega
  have h2 : x ≠ h-2 := by omega
  have h3 : x ≠ h-3 := by omega
  simp [zeroLeftPrefixTape, setBit, h0, h1, h2, h3]

theorem zeroLeftPrefix_run (b : Conf)
    (hq : b.q = .B) (h0 : b.tape b.h = false)
    (h1 : b.tape (b.h-1) = false)
    (h2 : b.tape (b.h-2) = false)
    (h3 : b.tape (b.h-3) = false) :
    shuttleRun 8 b =
      some ⟨.F,b.h,zeroLeftPrefixTape b.tape b.h⟩ := by
  rcases b with ⟨q,h,t⟩
  change q = .B at hq
  change t h = false at h0
  change t (h-1) = false at h1
  change t (h-2) = false at h2
  change t (h-3) = false at h3
  subst q
  simp (disch := omega) [shuttleRun, next, setBit,
    zeroLeftPrefixTape, h0, h1, h2, h3]

/-- Exact output tape after the even D/F sweep and its D0/E0/A0 return. -/
def evenSweepB0Tape (n : Nat) (t : Int → Bool) (h : Int) : Int → Bool :=
  setBit (setBit (evenSweepTape n t h) (h+2*(n:Int)-1) true)
    (h+2*(n:Int)) true

/-- The even sweep does not write strictly to the left of its initial head. -/
theorem evenSweepTape_left (n : Nat) (t : Int → Bool) (h x : Int)
    (hx : x ≤ h-1) : evenSweepTape n t h x = t x := by
  induction n generalizing t h with
  | zero =>
      simp [evenSweepTape]
  | succ n ih =>
      simp only [evenSweepTape]
      have htail := ih (setBit (setBit t h true) (h+1) false)
        (h+2) (by omega)
      rw [htail]
      simp (disch := omega) [setBit]

theorem evenSweepB0Tape_head (n : Nat) (t : Int → Bool) (h : Int)
    (hz : t (h+2*(n:Int)+1) = false) :
    evenSweepB0Tape n t h (h+2*(n:Int)+1) = false := by
  have hkeep := evenSweepTape_right n t h
    (h+2*(n:Int)+1) (by omega)
  have hne1 : h+2*(n:Int)+1 ≠ h+2*(n:Int)-1 := by omega
  have hne2 : h+2*(n:Int)+1 ≠ h+2*(n:Int) := by omega
  simp [evenSweepB0Tape,setBit,hkeep,hne1,hne2,hz]

/-- An even D/F sweep followed by D0/E0/A0 returns to B/0. The full output
    tape is retained; the two terminal writes are included explicitly. -/
theorem evenSweep_to_Bzero_exact (n : Nat) (t : Int → Bool) (h : Int)
    (hones : ∀ j : Nat, j < 2*n → t (h+(j:Int)) = true)
    (hzero : t (h+2*(n:Int)) = false)
    (hzeroNext : t (h+2*(n:Int)+1) = false)
    (hprev : n = 0 → t (h-1) = false) :
    shuttleRun (2*n+3) ⟨.D,h,t⟩ =
      some ⟨.B,h+2*(n:Int)+1,evenSweepB0Tape n t h⟩ ∧
    evenSweepB0Tape n t h (h+2*(n:Int)+1) = false := by
  let s := evenSweepTape n t h
  let p : Int := h+2*(n:Int)
  have hsweep : shuttleRun (2*n) ⟨.D,h,t⟩ =
      some ⟨.D,p,s⟩ := by
    simpa [p,s] using evenSweep n t h hones
  have hp0 : s p = false := by
    dsimp [s,p]
    rw [evenSweepTape_right n t h (h+2*(n:Int)) (by omega)]
    exact hzero
  have hpPrev : s (p-1) = false := by
    cases n with
    | zero =>
        simpa [s,p,evenSweepTape] using hprev rfl
    | succ k =>
        simpa [s,p] using evenSweepTape_last k t h
  let t1 := setBit s p false
  let t2 := setBit t1 (p-1) true
  let t3 := setBit t2 p true
  have ht1 : t1 = s := shuttleSetBit_same s p false hp0
  have hEread : t1 (p-1) = false := by
    rw [ht1]
    exact hpPrev
  have hAread : t2 p = false := by
    simp [t2,t1,setBit,show p ≠ p-1 by omega,hp0]
  have hs1 : next ⟨.D,p,s⟩ = some ⟨.E,p-1,t1⟩ := by
    simp [next,hp0,t1]
  have hs2 : next ⟨.E,p-1,t1⟩ = some ⟨.A,p,t2⟩ := by
    simp [next,hEread,t1,t2]
  have hs3 : next ⟨.A,p,t2⟩ = some ⟨.B,p+1,t3⟩ := by
    simp [next,hAread,t3,t2,t1]
  have htail : shuttleRun 3 ⟨.D,p,s⟩ = some ⟨.B,p+1,t3⟩ := by
    simp [shuttleRun,hs1,hs2,hs3]
  have hrun : shuttleRun (2*n+3) ⟨.D,h,t⟩ =
      some ⟨.B,h+2*(n:Int)+1,evenSweepB0Tape n t h⟩ := by
    calc
      shuttleRun (2*n+3) ⟨.D,h,t⟩ =
          (shuttleRun (2*n) ⟨.D,h,t⟩).bind (shuttleRun 3) := by
            simpa using shuttleRun_add (2*n) 3 ⟨.D,h,t⟩
      _ = shuttleRun 3 ⟨.D,p,s⟩ := by simp [hsweep,p,s]
      _ = some ⟨.B,h+2*(n:Int)+1,evenSweepB0Tape n t h⟩ := by
            simpa [evenSweepB0Tape,p,s,t3,t2,t1,ht1] using htail
  have hhead := evenSweepB0Tape_head n t h hzeroNext
  exact ⟨hrun,hhead⟩

/-- The B/0 output of the zero-left macro: an even right run is swept into
    alternating 10 cells, followed by the terminal 11 marker. -/
def zeroLeftEvenOutTape (n : Nat) (t : Int → Bool) (h : Int) : Int → Bool :=
  evenSweepB0Tape n (setBit (zeroLeftPrefixTape t h) h false) (h+1)

/-- The macro's output head cell is untouched, so the return really is B/0. -/
theorem zeroLeftEvenOutTape_head (n : Nat) (t : Int → Bool) (h : Int)
    (hz : t (h+2*(n:Int)+2) = false) :
    zeroLeftEvenOutTape n t h (h+2*(n:Int)+2) = false := by
  have hidx : h+1+2*(n:Int)+1 = h+2*(n:Int)+2 := by omega
  have hf : (setBit (zeroLeftPrefixTape t h) h false)
      (h+1+2*(n:Int)+1) = false := by
    rw [hidx]
    have hp := zeroLeftPrefixTape_right t h
      (h+2*(n:Int)+2) (by omega)
    have hne : h+2*(n:Int)+2 ≠ h := by omega
    simp [setBit,hp,hne,hz]
  simpa [zeroLeftEvenOutTape] using
    evenSweepB0Tape_head n (setBit (zeroLeftPrefixTape t h) h false)
      (h+1) hf

/-- Every B/0 with three zero cells to its left and a right corridor
    1^(2n)00 has an exact source-machine return after 2n+12 steps.
    The returned head is h+2n+2 and the complete output tape is specified. -/
theorem zeroLeftEvenRun_exact (n : Nat) (b : Conf)
    (hq : b.q = .B) (h0 : b.tape b.h = false)
    (h1 : b.tape (b.h-1) = false)
    (h2 : b.tape (b.h-2) = false)
    (h3 : b.tape (b.h-3) = false)
    (hones : ∀ j : Nat, j < 2*n →
      b.tape (b.h+1+(j:Int)) = true)
    (hzero : b.tape (b.h+2*(n:Int)+1) = false)
    (hzeroNext : b.tape (b.h+2*(n:Int)+2) = false) :
    shuttleRun (2*n+12) b =
      some ⟨.B,b.h+2*(n:Int)+2,zeroLeftEvenOutTape n b.tape b.h⟩ := by
  let f : Conf := ⟨.F,b.h,zeroLeftPrefixTape b.tape b.h⟩
  let fTape : Int → Bool :=
    setBit (zeroLeftPrefixTape b.tape b.h) b.h false
  let d : Conf := ⟨.D,b.h+1,fTape⟩
  have hprefix : shuttleRun 8 b = some f := by
    simpa [f] using zeroLeftPrefix_run b hq h0 h1 h2 h3
  have hFread : zeroLeftPrefixTape b.tape b.h b.h = true :=
    zeroLeftPrefixTape_head b.tape b.h
  have hFstep : shuttleRun 1 f = some d := by
    simp [shuttleRun,next,f,d,fTape,hFread]
  have hfAway (x : Int) (hx : b.h < x) : fTape x = b.tape x := by
    have hp := zeroLeftPrefixTape_right b.tape b.h x hx
    have hne : x ≠ b.h := by omega
    simp [fTape,setBit,hne,hp]
  have hFzero : fTape b.h = false := by
    simp [fTape,zeroLeftPrefixTape,setBit]
  have hones' : ∀ j : Nat, j < 2*n →
      fTape (b.h+1+(j:Int)) = true := by
    intro j hj
    calc
      fTape (b.h+1+(j:Int)) = b.tape (b.h+1+(j:Int)) :=
        hfAway _ (by omega)
      _ = true := hones j hj
  have hzero' : fTape (b.h+1+2*(n:Int)) = false := by
    calc
      fTape (b.h+1+2*(n:Int)) = b.tape (b.h+1+2*(n:Int)) :=
        hfAway _ (by omega)
      _ = false := by convert hzero using 1 <;> omega
  have hzeroNext' : fTape (b.h+1+2*(n:Int)+1) = false := by
    calc
      fTape (b.h+1+2*(n:Int)+1) = b.tape (b.h+1+2*(n:Int)+1) :=
        hfAway _ (by omega)
      _ = false := by convert hzeroNext using 1 <;> omega
  have hprev' : n = 0 → fTape ((b.h+1)-1) = false := by
    intro hn
    have heq : (b.h+1)-1 = b.h := by omega
    rw [heq]
    exact hFzero
  have htail := evenSweep_to_Bzero_exact n fTape (b.h+1)
    hones' hzero' hzeroNext' hprev'
  have hlen : 2*n+12 = 8+(1+(2*n+3)) := by omega
  calc
    shuttleRun (2*n+12) b =
        (shuttleRun 8 b).bind (shuttleRun (1+(2*n+3))) := by
          rw [hlen,shuttleRun_add]
    _ = shuttleRun (1+(2*n+3)) f := by rw [hprefix]; rfl
    _ = (shuttleRun 1 f).bind (shuttleRun (2*n+3)) := by
          rw [shuttleRun_add]
    _ = some ⟨.B,b.h+2*(n:Int)+2,zeroLeftEvenOutTape n b.tape b.h⟩ := by
          rw [hFstep]
          simp only [Option.bind_some]
          have hhead : b.h+1+2*(n:Int)+1 = b.h+2*(n:Int)+2 := by omega
          simpa [d,zeroLeftEvenOutTape,fTape,hhead] using htail.1

theorem zeroLeftEvenRun_returns_Bzero (n : Nat) (b : Conf)
    (hq : b.q = .B) (h0 : b.tape b.h = false)
    (h1 : b.tape (b.h-1) = false)
    (h2 : b.tape (b.h-2) = false)
    (h3 : b.tape (b.h-3) = false)
    (hones : ∀ j : Nat, j < 2*n →
      b.tape (b.h+1+(j:Int)) = true)
    (hzero : b.tape (b.h+2*(n:Int)+1) = false)
    (hzeroNext : b.tape (b.h+2*(n:Int)+2) = false) :
    ∃ d, shuttleRun (2*n+12) b = some d ∧
      d.q = .B ∧ d.h = b.h+2*(n:Int)+2 ∧ d.tape d.h = false := by
  let d : Conf := ⟨.B,b.h+2*(n:Int)+2,
    zeroLeftEvenOutTape n b.tape b.h⟩
  refine ⟨d,?_,rfl,rfl,?_⟩
  · simpa [d] using zeroLeftEvenRun_exact n b hq h0 h1 h2 h3
      hones hzero hzeroNext
  · change zeroLeftEvenOutTape n b.tape b.h
      (b.h+2*(n:Int)+2) = false
    exact zeroLeftEvenOutTape_head n b.tape b.h hzeroNext

/-- The macro preserves the entire left exterior of its four-cell prefix. -/
theorem zeroLeftEvenOutTape_left (n : Nat) (t : Int → Bool) (h x : Int)
    (hx : x ≤ h-4) : zeroLeftEvenOutTape n t h x = t x := by
  dsimp [zeroLeftEvenOutTape,evenSweepB0Tape]
  have hs := evenSweepTape_left n
    (setBit (zeroLeftPrefixTape t h) h false) (h+1) x (by omega)
  have hn1 : x ≠ h+2*(n:Int)-1 := by omega
  have hn2 : x ≠ h+2*(n:Int) := by omega
  have hn3 : x ≠ h := by omega
  have hn4 : x ≠ h-1 := by omega
  have hn5 : x ≠ h-2 := by omega
  have hn6 : x ≠ h-3 := by omega
  simp [setBit,zeroLeftPrefixTape,hs,hn1,hn2,hn3,hn4,hn5,hn6]

/-- The macro preserves the complete right exterior beginning at its new head. -/
theorem zeroLeftEvenOutTape_right (n : Nat) (t : Int → Bool) (h x : Int)
    (hx : h+2*(n:Int)+2 ≤ x) : zeroLeftEvenOutTape n t h x = t x := by
  dsimp [zeroLeftEvenOutTape,evenSweepB0Tape]
  have hs := evenSweepTape_right n
    (setBit (zeroLeftPrefixTape t h) h false) (h+1) x (by omega)
  have hn1 : x ≠ h+2*(n:Int)-1 := by omega
  have hn2 : x ≠ h+2*(n:Int) := by omega
  have hn3 : x ≠ h := by omega
  have hn4 : x ≠ h-1 := by omega
  have hn5 : x ≠ h-2 := by omega
  have hn6 : x ≠ h-3 := by omega
  simp [setBit,zeroLeftPrefixTape,hs,hn1,hn2,hn3,hn4,hn5,hn6]

#print axioms BB6Root119.zeroLeftEvenRun_exact
#print axioms BB6Root119.zeroLeftEvenRun_returns_Bzero
#print axioms BB6Root119.zeroLeftEvenOutTape_left
#print axioms BB6Root119.zeroLeftEvenOutTape_right

end BB6Root119
