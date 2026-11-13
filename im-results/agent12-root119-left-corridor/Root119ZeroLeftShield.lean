import Root119ZeroLeftEvenRun
set_option linter.unusedSimpArgs false
namespace BB6Root119
/-- The tape-level form of NoLeft4 true true false: no 1100 word ends strictly before the head. -/
theorem evenSweepTape_no_adjacent_ones (n : Nat) (t : Int → Bool)
    (h x : Int) (hx : h ≤ x) (hxEnd : x+1 < h+2*(n:Int)) :
    ¬ (evenSweepTape n t h x = true ∧
       evenSweepTape n t h (x+1) = true) := by
  induction n generalizing t h x with
  | zero => omega
  | succ n ih =>
      simp only [evenSweepTape]
      by_cases h0 : x = h
      · subst x
        have hneq : h ≠ h+1 := by omega
        have hneq' : h+1 ≠ h := by omega
        have hleft0 :
            evenSweepTape n (setBit (setBit t h true) (h+1) false)
              (h+2) h = true := by
          rw [evenSweepTape_left n _ (h+2) h (by omega)]
          simp [setBit, hneq]
        have hleft1 :
            evenSweepTape n (setBit (setBit t h true) (h+1) false)
              (h+2) (h+1) = false := by
          rw [evenSweepTape_left n _ (h+2) (h+1) (by omega)]
          simp [setBit, hneq']
        simp [setBit, hleft0, hleft1, hneq, hneq']
      · by_cases h1 : x = h+1
        · subst x
          have hneq' : h+1 ≠ h := by omega
          have hleft :
              evenSweepTape n (setBit (setBit t h true) (h+1) false)
                (h+2) (h+1) = false := by
            rw [evenSweepTape_left n _ (h+2) (h+1) (by omega)]
            simp [setBit, hneq']
          simp [setBit, hleft, hneq']
        · have hx' : h+2 ≤ x := by omega
          have hEnd' : x+1 < (h+2)+2*(n:Int) := by omega
          exact ih (setBit (setBit t h true) (h+1) false)
            (h+2) x hx' hEnd'

theorem zeroLeftEvenOutTape_no_adjacent_ones (n : Nat) (t : Int → Bool)
    (h x : Int) (hx : h+2 ≤ x)
    (hxEnd : x+1 < h+2*(n:Int)) :
    ¬ (zeroLeftEvenOutTape n t h x = true ∧
       zeroLeftEvenOutTape n t h (x+1) = true) := by
  have hbase := evenSweepTape_no_adjacent_ones n
    (setBit (zeroLeftPrefixTape t h) h false) (h+1) x
    (by omega) (by omega)
  have h1 : x ≠ h+1+2*(n:Int)-1 := by omega
  have h2 : x ≠ h+1+2*(n:Int) := by omega
  have h3 : x+1 ≠ h+1+2*(n:Int)-1 := by omega
  have h4 : x+1 ≠ h+1+2*(n:Int) := by omega
  simpa [zeroLeftEvenOutTape, evenSweepB0Tape, setBit, h1, h2, h3, h4]
    using hbase

theorem zeroLeftEvenOutTape_hm3 (n : Nat) (t : Int → Bool) (h : Int) :
    zeroLeftEvenOutTape n t h (h-3) = true := by
  let fTape := setBit (zeroLeftPrefixTape t h) h false
  have hs : evenSweepTape n fTape (h+1) (h-3) = fTape (h-3) :=
    evenSweepTape_left n fTape (h+1) (h-3) (by omega)
  have h1 : h-3 ≠ h+1+2*(n:Int)-1 := by omega
  have h2 : h-3 ≠ h+1+2*(n:Int) := by omega
  have hp : fTape (h-3) = true := by
    simp [fTape, setBit, zeroLeftPrefixTape]
    omega
  change setBit (setBit (evenSweepTape n fTape (h+1))
    (h+1+2*(n:Int)-1) true) (h+1+2*(n:Int)) true (h-3) = true
  simp [setBit, h1, h2]
  rw [hs]
  simp [hp]

theorem zeroLeftEvenOutTape_hm2 (n : Nat) (t : Int → Bool) (h : Int) :
    zeroLeftEvenOutTape n t h (h-2) = false := by
  let fTape := setBit (zeroLeftPrefixTape t h) h false
  have hs : evenSweepTape n fTape (h+1) (h-2) = fTape (h-2) :=
    evenSweepTape_left n fTape (h+1) (h-2) (by omega)
  have h1 : h-2 ≠ h+1+2*(n:Int)-1 := by omega
  have h2 : h-2 ≠ h+1+2*(n:Int) := by omega
  have hp : fTape (h-2) = false := by
    simp [fTape, setBit, zeroLeftPrefixTape]
    omega
  change setBit (setBit (evenSweepTape n fTape (h+1))
    (h+1+2*(n:Int)-1) true) (h+1+2*(n:Int)) true (h-2) = false
  simp [setBit, h1, h2]
  rw [hs]
  simp [hp]

theorem zeroLeftEvenOutTape_hm1 (n : Nat) (t : Int → Bool) (h : Int) :
    zeroLeftEvenOutTape n t h (h-1) = true := by
  let fTape := setBit (zeroLeftPrefixTape t h) h false
  have hs : evenSweepTape n fTape (h+1) (h-1) = fTape (h-1) :=
    evenSweepTape_left n fTape (h+1) (h-1) (by omega)
  have h1 : h-1 ≠ h+1+2*(n:Int)-1 := by omega
  have h2 : h-1 ≠ h+1+2*(n:Int) := by omega
  have hp : fTape (h-1) = true := by
    simp [fTape, setBit, zeroLeftPrefixTape]
    omega
  change setBit (setBit (evenSweepTape n fTape (h+1))
    (h+1+2*(n:Int)-1) true) (h+1+2*(n:Int)) true (h-1) = true
  simp [setBit, h1, h2]
  rw [hs]
  simp [hp]

theorem zeroLeftEvenOutTape_h_false (n : Nat) (t : Int → Bool) (h : Int)
    (hn : 0 < n) : zeroLeftEvenOutTape n t h h = false := by
  let fTape := setBit (zeroLeftPrefixTape t h) h false
  have hs : evenSweepTape n fTape (h+1) h = fTape h :=
    evenSweepTape_left n fTape (h+1) h (by omega)
  have h1 : h ≠ h+1+2*(n:Int)-1 := by omega
  have h2 : h ≠ h+1+2*(n:Int) := by omega
  have hp : fTape h = false := by simp [fTape, setBit]
  change setBit (setBit (evenSweepTape n fTape (h+1))
    (h+1+2*(n:Int)-1) true) (h+1+2*(n:Int)) true h = false
  simp [setBit, h1, h2]
  rw [hs]
  simp [hp]

theorem zeroLeftEvenOutTape_h1_true (n : Nat) (t : Int → Bool) (h : Int) :
    zeroLeftEvenOutTape n t h (h+1) = true := by
  by_cases hn : n = 0
  · subst n
    simp [zeroLeftEvenOutTape, evenSweepB0Tape, evenSweepTape, setBit]
  · have hnpos : 0 < n := by omega
    let fTape := setBit (zeroLeftPrefixTape t h) h false
    have hs : evenSweepTape n fTape (h+1) (h+1) = true := by
      cases n with
      | zero => omega
      | succ k =>
        simp only [evenSweepTape]
        have hleft := evenSweepTape_left k
          (setBit (setBit fTape (h+1) true) (h+2) false)
          (h+3) (h+1) (by omega)
        have hidx1 : h+1+1 = h+2 := by omega
        have hidx2 : h+1+2 = h+3 := by omega
        rw [hidx1, hidx2]
        rw [hleft]
        simp [setBit]
    have h1 : h+1 ≠ h+1+2*(n:Int)-1 := by omega
    have h2 : h+1 ≠ h+1+2*(n:Int) := by omega
    change setBit (setBit (evenSweepTape n fTape (h+1))
      (h+1+2*(n:Int)-1) true) (h+1+2*(n:Int)) true (h+1) = true
    simp [setBit, h1, h2]
    rw [hs]

theorem zeroLeftEvenOutTape_h2_false (n : Nat) (t : Int → Bool) (h : Int)
    (hn : 2 ≤ n) : zeroLeftEvenOutTape n t h (h+2) = false := by
  let fTape := setBit (zeroLeftPrefixTape t h) h false
  have hfirst : evenSweepTape n fTape (h+1) (h+1) = true := by
    cases n with
    | zero => omega
    | succ k =>
      simp only [evenSweepTape]
      have hleft := evenSweepTape_left k
        (setBit (setBit fTape (h+1) true) (h+2) false)
        (h+3) (h+1) (by omega)
      have hidx1 : h+1+1 = h+2 := by omega
      have hidx2 : h+1+2 = h+3 := by omega
      rw [hidx1, hidx2]
      rw [hleft]
      simp [setBit]
  have hpair := evenSweepTape_no_adjacent_ones n fTape (h+1) (h+1)
    (by omega) (by omega)
  have hsecond : evenSweepTape n fTape (h+1) (h+2) = false := by
    cases hv : evenSweepTape n fTape (h+1) (h+2) with
    | false => rfl
    | true =>
      have hv' : evenSweepTape n fTape (h+1) (h+1+1) = true := by
        simpa [show h+1+1 = h+2 by omega] using hv
      exact False.elim (hpair ⟨hfirst,hv'⟩)
  have h1 : h+2 ≠ h+1+2*(n:Int)-1 := by omega
  have h2 : h+2 ≠ h+1+2*(n:Int) := by omega
  change setBit (setBit (evenSweepTape n fTape (h+1))
    (h+1+2*(n:Int)-1) true) (h+1+2*(n:Int)) true (h+2) = false
  simp [setBit, h1, h2]
  exact hsecond

def NoLeft1100 (t : Int → Bool) (h : Int) : Prop :=
  ∀ x : Int, x+3 < h →
    ¬(t x = true ∧ t (x+1) = true ∧
      t (x+2) = false ∧ t (x+3) = false)

theorem zeroLeftEvenOutTape_preserves_NoLeft1100
    (n : Nat) (t : Int → Bool) (h : Int)
    (hs : NoLeft1100 t h) :
    NoLeft1100 (zeroLeftEvenOutTape n t h) (h+2*(n:Int)+2) := by
  intro x hx hbad
  by_cases hfar : x ≤ h-7
  · have h0 := zeroLeftEvenOutTape_left n t h x (by omega)
    have h1 := zeroLeftEvenOutTape_left n t h (x+1) (by omega)
    have h2 := zeroLeftEvenOutTape_left n t h (x+2) (by omega)
    have h3 := zeroLeftEvenOutTape_left n t h (x+3) (by omega)
    have hsource : t x = true ∧ t (x+1) = true ∧
        t (x+2) = false ∧ t (x+3) = false := by
      rw [← h0, ← h1, ← h2, ← h3]
      exact hbad
    exact hs x (by omega) hsource
  · have hlow : h-6 ≤ x := by omega
    by_cases hn0 : n = 0
    · subst n
      have hupper : x ≤ h-2 := by omega
      have hcases : x = h-6 ∨ x = h-5 ∨ x = h-4 ∨
          x = h-3 ∨ x = h-2 := by omega
      rcases hcases with hcase | hcase | hcase | hcase | hcase
      · subst x
        have hv := zeroLeftEvenOutTape_hm3 0 t h
        have hbad' : zeroLeftEvenOutTape 0 t h (h-3) = false := by
          have hi : h-6+3 = h-3 := by omega
          simpa [hi] using hbad.2.2.2
        rw [hv] at hbad'
        cases hbad'
      · subst x
        have hv := zeroLeftEvenOutTape_hm3 0 t h
        have hbad' : zeroLeftEvenOutTape 0 t h (h-3) = false := by
          have hi : h-5+2 = h-3 := by omega
          simpa [hi] using hbad.2.2.1
        rw [hv] at hbad'
        cases hbad'
      · subst x
        have hv := zeroLeftEvenOutTape_hm1 0 t h
        have hbad' : zeroLeftEvenOutTape 0 t h (h-1) = false := by
          have hi : h-4+3 = h-1 := by omega
          simpa [hi] using hbad.2.2.2
        rw [hv] at hbad'
        cases hbad'
      · subst x
        have hv := zeroLeftEvenOutTape_hm2 0 t h
        have hbad' : zeroLeftEvenOutTape 0 t h (h-2) = true := by
          have hi : h-3+1 = h-2 := by omega
          simpa [hi] using hbad.2.1
        rw [hv] at hbad'
        cases hbad'
      · subst x
        have hv := zeroLeftEvenOutTape_hm2 0 t h
        rw [hv] at hbad
        cases hbad.1
    · have hnpos : 0 < n := by omega
      have hupper : x ≤ h+2*(n:Int)-2 := by omega
      by_cases hnear : x ≤ h+1
      · have hcases : x = h-6 ∨ x = h-5 ∨ x = h-4 ∨
          x = h-3 ∨ x = h-2 ∨ x = h-1 ∨ x = h ∨ x = h+1 := by omega
        rcases hcases with hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase
        · subst x
          have hv := zeroLeftEvenOutTape_hm3 n t h
          have hbad' : zeroLeftEvenOutTape n t h (h-3) = false := by
            have hi : h-6+3 = h-3 := by omega
            simpa [hi] using hbad.2.2.2
          rw [hv] at hbad'
          cases hbad'
        · subst x
          have hv := zeroLeftEvenOutTape_hm3 n t h
          have hbad' : zeroLeftEvenOutTape n t h (h-3) = false := by
            have hi : h-5+2 = h-3 := by omega
            simpa [hi] using hbad.2.2.1
          rw [hv] at hbad'
          cases hbad'
        · subst x
          have hv := zeroLeftEvenOutTape_hm1 n t h
          have hbad' : zeroLeftEvenOutTape n t h (h-1) = false := by
            have hi : h-4+3 = h-1 := by omega
            simpa [hi] using hbad.2.2.2
          rw [hv] at hbad'
          cases hbad'
        · subst x
          have hv := zeroLeftEvenOutTape_hm2 n t h
          have hbad' : zeroLeftEvenOutTape n t h (h-2) = true := by
            have hi : h-3+1 = h-2 := by omega
            simpa [hi] using hbad.2.1
          rw [hv] at hbad'
          cases hbad'
        · subst x
          have hv := zeroLeftEvenOutTape_hm2 n t h
          rw [hv] at hbad
          cases hbad.1
        · subst x
          have hv := zeroLeftEvenOutTape_h_false n t h hnpos
          have hbad' : zeroLeftEvenOutTape n t h h = true := by
            have hi : h-1+1 = h := by omega
            simpa [hi] using hbad.2.1
          rw [hv] at hbad'
          cases hbad'
        · subst x
          have hv := zeroLeftEvenOutTape_h_false n t h hnpos
          rw [hv] at hbad
          cases hbad.1
        · subst x
          have htwo : 2 ≤ n := by omega
          have hv := zeroLeftEvenOutTape_h2_false n t h htwo
          have hbad' : zeroLeftEvenOutTape n t h (h+2) = true := by
            have hi : h+1+1 = h+2 := by omega
            simpa [hi] using hbad.2.1
          rw [hv] at hbad'
          cases hbad'
      · have hxStart : h+2 ≤ x := by omega
        have hxEnd : x+1 < h+2*(n:Int) := by omega
        exact zeroLeftEvenOutTape_no_adjacent_ones n t h x
          hxStart hxEnd ⟨hbad.1,hbad.2.1⟩

/-- Exact return and shield transport in one reusable conditional macro theorem. -/
theorem zeroLeftEvenRun_exact_with_NoLeft1100
    (n : Nat) (b : Conf)
    (hq : b.q = .B) (h0 : b.tape b.h = false)
    (h1 : b.tape (b.h-1) = false)
    (h2 : b.tape (b.h-2) = false)
    (h3 : b.tape (b.h-3) = false)
    (hones : ∀ j : Nat, j < 2*n →
      b.tape (b.h+1+(j:Int)) = true)
    (hzero : b.tape (b.h+2*(n:Int)+1) = false)
    (hzeroNext : b.tape (b.h+2*(n:Int)+2) = false)
    (hs : NoLeft1100 b.tape b.h) :
    shuttleRun (2*n+12) b =
      some ⟨.B,b.h+2*(n:Int)+2,zeroLeftEvenOutTape n b.tape b.h⟩ ∧
    NoLeft1100 (zeroLeftEvenOutTape n b.tape b.h)
      (b.h+2*(n:Int)+2) := by
  exact ⟨zeroLeftEvenRun_exact n b hq h0 h1 h2 h3 hones hzero hzeroNext,
    zeroLeftEvenOutTape_preserves_NoLeft1100 n b.tape b.h hs⟩

#print axioms BB6Root119.zeroLeftEvenRun_exact_with_NoLeft1100

#print axioms BB6Root119.zeroLeftEvenOutTape_preserves_NoLeft1100
end BB6Root119
