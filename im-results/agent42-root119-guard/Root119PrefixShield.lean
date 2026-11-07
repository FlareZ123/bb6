import Root119OddEvenChain
import Root119BShield

namespace BB6Root119

theorem evenSweepTape_left (n : Nat) (t : Int → Bool) (h x : Int)
    (hx : x < h) : evenSweepTape n t h x = t x := by
  induction n generalizing t h x with
  | zero => rfl
  | succ n ih =>
      change evenSweepTape n (setBit (setBit t h true) (h+1) false) (h+2) x = t x
      rw [ih (setBit (setBit t h true) (h+1) false) (h+2) x (by omega)]
      have hne0 : x ≠ h := by omega
      have hne1 : x ≠ h+1 := by omega
      simp [setBit,hne0,hne1]

theorem evenSweepTape_head (n : Nat) (t : Int → Bool) (h : Int) :
    evenSweepTape (n+1) t h h = true := by
  change evenSweepTape n (setBit (setBit t h true) (h+1) false) (h+2) h = true
  rw [evenSweepTape_left n (setBit (setBit t h true) (h+1) false) (h+2) h (by omega)]
  have hne : h ≠ h+1 := by omega
  simp [setBit,hne]

theorem evenSweepBResultTape_head (n : Nat) (t : Int → Bool) (h : Int) :
    evenSweepBResultTape n t h h = true := by
  have hhead : evenSweepTape (n+1) t h h = true := evenSweepTape_head n t h
  have hp : h ≠ h+2*(n+1) := by omega
  have hp1 : h ≠ h+2*(n+1)-1 := by omega
  simp only [evenSweepBResultTape, setBit, if_neg hp, if_neg hp1, hhead]

theorem evenSweepBResultTape_shift (n : Nat) (t : Int → Bool) (h : Int) :
    evenSweepBResultTape (n+1) t h =
      evenSweepBResultTape n (setBit (setBit t h true) (h+1) false) (h+2) := by
  funext x
  simp only [evenSweepBResultTape, evenSweepTape]
  have hp : h+2*((↑(n+1:Nat):Int)+1) = h+2+2*((↑n:Int)+1) := by omega
  rw [hp]

theorem evenSweepBResultTape_no_adjacent_zero (n : Nat) (t : Int → Bool) (h x : Int)
    (hlo : h-1 ≤ x) (hhi : x < h+2*(n+1)) :
    evenSweepBResultTape n t h x = true ∨
      evenSweepBResultTape n t h (x+1) = true := by
  induction n generalizing t h x with
  | zero =>
      have hx : x = h-1 ∨ x = h ∨ x = h+1 := by omega
      rcases hx with h0 | h1 | h2
      · subst x
        right
        have hpos : h-1+1 = h := by omega
        rw [hpos]
        exact evenSweepBResultTape_head 0 t h
      · subst x
        left
        exact evenSweepBResultTape_head 0 t h
      · subst x
        left
        simp [evenSweepBResultTape,evenSweepTape,setBit] <;> omega
  | succ n ih =>
      have hx : x = h-1 ∨ x = h ∨ h+1 ≤ x := by omega
      rcases hx with h0 | h1 | h2
      · subst x
        right
        have hpos : h-1+1 = h := by omega
        rw [hpos]
        exact evenSweepBResultTape_head (n+1) t h
      · subst x
        left
        exact evenSweepBResultTape_head (n+1) t h
      · rw [evenSweepBResultTape_shift]
        have hlo' : (h+2)-1 ≤ x := by omega
        have hhi' : x < (h+2)+2*(n+1) := by omega
        exact ih (setBit (setBit t h true) (h+1) false) (h+2) x hlo' hhi'

theorem evenSweepBResultTape_left (n : Nat) (t : Int → Bool) (h x : Int)
    (hx : x < h) : evenSweepBResultTape n t h x = t x := by
  have hp : x ≠ h+2*(n+1) := by omega
  have hp1 : x ≠ h+2*(n+1)-1 := by omega
  have hleft : evenSweepTape (n+1) t h x = t x := evenSweepTape_left (n+1) t h x hx
  simp only [evenSweepBResultTape, setBit, if_neg hp, if_neg hp1, hleft]

theorem evenSweepBResultTape_preserves_NoLeft4 (n : Nat) (t : Int → Bool) (h : Int)
    (hs : NoLeft4 true true false (⟨.D,h,t⟩ : Conf)) :
    NoLeft4 true true false
      (⟨.B,h+2*(n+1)+1,evenSweepBResultTape n t h⟩ : Conf) := by
  intro x hx hw
  change x+3 < h+2*(n+1)+1 at hx
  by_cases hfar : x+3 < h
  · have hw' : t x = true ∧ t (x+1) = true ∧
        t (x+2) = false ∧ t (x+3) = false := by
      rcases hw with ⟨h0,h1,h2,h3⟩
      exact ⟨by simpa [evenSweepBResultTape_left n t h x (by omega)] using h0,
        by simpa [evenSweepBResultTape_left n t h (x+1) (by omega)] using h1,
        by simpa [evenSweepBResultTape_left n t h (x+2) (by omega)] using h2,
        by simpa [evenSweepBResultTape_left n t h (x+3) (by omega)] using h3⟩
    exact hs x (by omega) hw'
  · have hlo : h-1 ≤ x+2 := by omega
    have hhi : x+2 < h+2*(n+1) := by omega
    have hpair := evenSweepBResultTape_no_adjacent_zero n t h (x+2) hlo hhi
    have hfalse2 : evenSweepBResultTape n t h (x+2) = false := by simpa using hw.2.2.1
    have hfalse3 : evenSweepBResultTape n t h (x+3) = false := by simpa using hw.2.2.2
    rcases hpair with htrue | htrue
    · simp [hfalse2] at htrue
    · have hidx : x+2+1 = x+3 := by omega
      rw [hidx] at htrue
      simp [hfalse3] at htrue

theorem twoWavePrefixTape_left (t : Int → Bool) (h x : Int)
    (hx : x < h-3) : twoWavePrefixTape t h x = t x := by
  simp [twoWavePrefixTape,setBit,
    show x ≠ h-3 by omega,show x ≠ h-2 by omega,
    show x ≠ h-1 by omega,show x ≠ h by omega]

theorem noLeft4_twoWavePrefix (b : Conf)
    (hs : NoLeft4 true true false b) :
    NoLeft4 true true false (⟨.F,b.h-1,twoWavePrefixTape b.tape b.h⟩ : Conf) := by
  intro x hx hw
  have hbound : x+3 < b.h-1 := by simpa using hx
  by_cases hfar : x+3 ≤ b.h-4
  · have hw' : b.tape x = true ∧ b.tape (x+1) = true ∧
        b.tape (x+2) = false ∧ b.tape (x+3) = false := by
      rcases hw with ⟨h0,h1,h2,h3⟩
      have h0' : twoWavePrefixTape b.tape b.h x = true := by change _ = true at h0; exact h0
      have h1' : twoWavePrefixTape b.tape b.h (x+1) = true := by change _ = true at h1; exact h1
      have h2' : twoWavePrefixTape b.tape b.h (x+2) = false := by change _ = false at h2; exact h2
      have h3' : twoWavePrefixTape b.tape b.h (x+3) = false := by change _ = false at h3; exact h3
      exact ⟨by rw [twoWavePrefixTape_left b.tape b.h x (by omega)] at h0'; exact h0',
        by rw [twoWavePrefixTape_left b.tape b.h (x+1) (by omega)] at h1'; exact h1',
        by rw [twoWavePrefixTape_left b.tape b.h (x+2) (by omega)] at h2'; exact h2',
        by rw [twoWavePrefixTape_left b.tape b.h (x+3) (by omega)] at h3'; exact h3'⟩
    exact hs x (by omega) hw'
  · have hcase : x+3 = b.h-3 ∨ x+3 = b.h-2 := by omega
    rcases hcase with h3 | h2
    · have hlast : twoWavePrefixTape b.tape b.h (x+3) = true := by
        rw [h3]
        simp [twoWavePrefixTape,setBit]
      have hfalse : twoWavePrefixTape b.tape b.h (x+3) = false := hw.2.2.2
      rw [hlast] at hfalse
      contradiction
    · have hlast : twoWavePrefixTape b.tape b.h (x+3) = true := by
        rw [h2]
        simp [twoWavePrefixTape,setBit]
      have hfalse : twoWavePrefixTape b.tape b.h (x+3) = false := hw.2.2.2
      rw [hlast] at hfalse
      contradiction

theorem noLeft4_left_shift (p q r : Bool) (c d : Conf)
    (hpos : d.h = c.h-1)
    (hsame : ∀ x : Int, x ≤ c.h-2 → d.tape x = c.tape x)
    (hs : NoLeft4 p q r c) : NoLeft4 p q r d := by
  intro x hx hw
  have hxold : x+3 < c.h := by rw [hpos] at hx; omega
  rcases hw with ⟨h0,h1,h2,h3⟩
  have hword : c.tape x = p ∧ c.tape (x+1) = q ∧
      c.tape (x+2) = r ∧ c.tape (x+3) = false := by
    exact ⟨(hsame x (by omega)).symm.trans h0,
      (hsame (x+1) (by omega)).symm.trans h1,
      (hsame (x+2) (by omega)).symm.trans h2,
      (hsame (x+3) (by omega)).symm.trans h3⟩
  exact hs x hxold hword

theorem noLeft4_right_write_false (p q r : Bool) (c d : Conf)
    (hpos : d.h = c.h+1)
    (hprev : d.tape (c.h-1) ≠ r)
    (hsame : ∀ x : Int, x ≠ c.h → d.tape x = c.tape x)
    (hs : NoLeft4 p q r c) : NoLeft4 p q r d := by
  intro x hx hw
  by_cases hlt : x+3 < c.h
  · rcases hw with ⟨h0,h1,h2,h3⟩
    have hword : c.tape x = p ∧ c.tape (x+1) = q ∧
        c.tape (x+2) = r ∧ c.tape (x+3) = false := by
      exact ⟨(hsame x (by omega)).symm.trans h0,
        (hsame (x+1) (by omega)).symm.trans h1,
        (hsame (x+2) (by omega)).symm.trans h2,
        (hsame (x+3) (by omega)).symm.trans h3⟩
    exact hs x hlt hword
  · have heq : x+3 = c.h := by rw [hpos] at hx; omega
    have hidx : x+2 = c.h-1 := by omega
    have hwordLast : d.tape (c.h-1) = r := by rw [← hidx]; exact hw.2.2.1
    exact hprev hwordLast

theorem noLeft4_right_boundary (p q r : Bool) (c d : Conf)
    (hpos : d.h = c.h+1)
    (hsame : ∀ x : Int, x ≠ c.h → d.tape x = c.tape x)
    (hboundary : ¬(c.tape (c.h-3) = p ∧ c.tape (c.h-2) = q ∧
      c.tape (c.h-1) = r))
    (hs : NoLeft4 p q r c) : NoLeft4 p q r d := by
  intro x hx hw
  by_cases hlt : x+3 < c.h
  · rcases hw with ⟨h0,h1,h2,h3⟩
    have hword : c.tape x = p ∧ c.tape (x+1) = q ∧
        c.tape (x+2) = r ∧ c.tape (x+3) = false := by
      exact ⟨(hsame x (by omega)).symm.trans h0,
        (hsame (x+1) (by omega)).symm.trans h1,
        (hsame (x+2) (by omega)).symm.trans h2,
        (hsame (x+3) (by omega)).symm.trans h3⟩
    exact hs x hlt hword
  · have heq : x+3 = c.h := by rw [hpos] at hx; omega
    have hidx1 : x = c.h-3 := by omega
    have hidx2 : x+1 = c.h-2 := by omega
    have hidx3 : x+2 = c.h-1 := by omega
    apply hboundary
    rcases hw with ⟨h0,h1,h2,h3⟩
    exact ⟨by
        calc
          c.tape (c.h-3) = c.tape x := by rw [← hidx1]
          _ = d.tape x := (hsame x (by omega)).symm
          _ = p := h0,
      by
        calc
          c.tape (c.h-2) = c.tape (x+1) := by rw [← hidx2]
          _ = d.tape (x+1) := (hsame (x+1) (by omega)).symm
          _ = q := h1,
      by
        calc
          c.tape (c.h-1) = c.tape (x+2) := by rw [← hidx3]
          _ = d.tape (x+2) := (hsame (x+2) (by omega)).symm
          _ = r := h2⟩

theorem b0_even_prefix_to_b0_preserves_NoLeft4 (b : Conf) (n : Nat)
    (hb : Reach b) (hb0 : BZero b)
    (hleft : b.tape (b.h-1) = true)
    (hzero : b.tape (b.h-2) = false)
    (hone : b.tape (b.h-3) = true)
    (hones : ∀ j : Nat, j < 2*n+1 → b.tape (b.h+1+(j:Int)) = true)
    (hterminal : b.tape (b.h+(2*(n+1):Int)) = false)
    (hfinal : b.tape (b.h+(2*(n+1):Int)+1) = false)
    (hshield : NoLeft4 true true false b) :
    ∃ bout : Conf, run (2*n+15) b = some bout ∧ Reach bout ∧ BZero bout ∧
      NoLeft4 true true false bout := by
  obtain ⟨bout,hrun,hreach,hBzero,hhead,htape⟩ :=
    b0_even_prefix_to_b0_exact b n hb hb0 hleft hzero hone hones hterminal hfinal
  let f : Conf := ⟨.F,b.h-1,twoWavePrefixTape b.tape b.h⟩
  let d : Conf := ⟨.D,b.h,setBit (twoWavePrefixTape b.tape b.h) (b.h-1) false⟩
  have hfshield : NoLeft4 true true false f := by
    simpa [f] using noLeft4_twoWavePrefix b hshield
  have hpos : d.h = f.h+1 := by simp [d,f]
  have hprev : d.tape (f.h-1) ≠ false := by
    have hidx : f.h-1 = b.h-2 := by dsimp [f]; omega
    rw [hidx]
    have hne : b.h-2 ≠ b.h-1 := by omega
    simp [d,setBit,twoWavePrefixTape,hne]
  have hsame : ∀ x : Int, x ≠ f.h → d.tape x = f.tape x := by
    intro x hx
    simp [d,f,setBit,hx]
  have hdshield : NoLeft4 true true false d :=
    noLeft4_right_write_false true true false f d hpos hprev hsame hfshield
  have hout : NoLeft4 true true false
      (⟨.B,b.h+2*(n+1)+1,evenSweepBResultTape n d.tape d.h⟩ : Conf) := by
    simpa [d] using evenSweepBResultTape_preserves_NoLeft4 n d.tape d.h hdshield
  have heq : bout =
      (⟨.B,b.h+2*(n+1)+1,evenSweepBResultTape n d.tape d.h⟩ : Conf) := by
    cases bout with
    | mk q h t =>
      simp only [BZero] at hBzero
      simp_all [d]
  exact ⟨bout,hrun,hreach,hBzero,by rw [heq]; exact hout⟩

theorem b0_odd_even_chain_to_b0_preserves_NoLeft4 (b : Conf) (n : Nat)
    (hb : Reach b) (hb0 : BZero b)
    (hleft : b.tape (b.h-1) = true)
    (hzero : b.tape (b.h-2) = false)
    (hone : b.tape (b.h-3) = true)
    (hones : ∀ j : Nat, j < 2*n → b.tape (b.h+1+(j:Int)) = true)
    (hterminal1 : b.tape (b.h+(2*n+1:Int)) = false)
    (hterminal2 : b.tape (b.h+(2*n+2:Int)) = false)
    (hfinal : b.tape (b.h+(2*n+3:Int)) = false)
    (hshield : NoLeft4 true true false b)
    (hboundary : ¬(b.tape (b.h-6) = true ∧ b.tape (b.h-5) = true ∧
      b.tape (b.h-4) = false)) :
    ∃ bout : Conf, run (6*n+23) b = some bout ∧ Reach bout ∧ BZero bout ∧
      NoLeft4 true true false bout := by
  obtain ⟨bout,hrun,hreach,hBzero,hhead,htape⟩ :=
    b0_odd_even_chain_to_b0_exact b n hb hb0 hleft hzero hone hones
      hterminal1 hterminal2 hfinal
  let H : Int := b.h-1
  let t1 : Int → Bool := twoWavePrefixTape b.tape b.h
  let f1 : Conf := ⟨.F,H,t1⟩
  let b1 : Conf := ⟨.B,H-1,oddWaveTape n t1 H⟩
  let f2 : Conf := ⟨.F,H-2,setBit b1.tape (H-1) true⟩
  let d2 : Conf := ⟨.D,H-1,setBit f2.tape (H-2) false⟩
  have hf1shield : NoLeft4 true true false f1 := by
    simpa [f1,H,t1] using noLeft4_twoWavePrefix b hshield
  have hb1pos : b1.h = f1.h-1 := by simp [b1,f1,H]
  have hb1same : ∀ x : Int, x ≤ f1.h-2 → b1.tape x = f1.tape x := by
    intro x hx
    change oddWaveTape n t1 H x = t1 x
    have hx' : x ≤ H-2 := by simpa [f1] using hx
    exact oddWaveTape_left n t1 H x (by dsimp [H] at hx' ⊢; omega)
  have hb1shield : NoLeft4 true true false b1 :=
    noLeft4_left_shift true true false f1 b1 hb1pos hb1same hf1shield
  have hf2pos : f2.h = b1.h-1 := by dsimp [f2,b1,H]; omega
  have hf2same : ∀ x : Int, x ≤ b1.h-2 → f2.tape x = b1.tape x := by
    intro x hx
    have hx' : x ≤ H-3 := by dsimp [b1,H] at hx; omega
    have hne : x ≠ H-1 := by omega
    simp [f2,setBit,hne]
  have hf2shield : NoLeft4 true true false f2 :=
    noLeft4_left_shift true true false b1 f2 hf2pos hf2same hb1shield
  have hd2pos : d2.h = f2.h+1 := by dsimp [d2,f2,H]; omega
  have hd2same : ∀ x : Int, x ≠ f2.h → d2.tape x = f2.tape x := by
    intro x hx
    have hne : x ≠ H-2 := by
      have hx' : x ≠ f2.h := hx
      dsimp [f2,H] at hx'
      exact hx'
    simp [d2,setBit,hne]
  have hcell (x : Int) (hx : x ≤ b.h-4) : f2.tape x = b.tape x := by
    have hidx : H-1 = b.h-2 := by dsimp [H]; omega
    have hne : x ≠ H-1 := by rw [hidx]; omega
    calc
      f2.tape x = b1.tape x := by simp [f2,setBit,hne]
      _ = t1 x := oddWaveTape_left n t1 H x (by dsimp [H] at hx ⊢; omega)
      _ = b.tape x := twoWavePrefixTape_left b.tape b.h x (by omega)
  have hboundary2 : ¬(f2.tape (f2.h-3) = true ∧ f2.tape (f2.h-2) = true ∧
      f2.tape (f2.h-1) = false) := by
    intro hw
    apply hboundary
    have hidx1 : f2.h-3 = b.h-6 := by dsimp [f2,b1,H]; omega
    have hidx2 : f2.h-2 = b.h-5 := by dsimp [f2,b1,H]; omega
    have hidx3 : f2.h-1 = b.h-4 := by dsimp [f2,b1,H]; omega
    exact ⟨by
        calc
          b.tape (b.h-6) = f2.tape (b.h-6) := (hcell (b.h-6) (by omega)).symm
          _ = f2.tape (f2.h-3) := by rw [hidx1]
          _ = true := hw.1,
      by
        calc
          b.tape (b.h-5) = f2.tape (b.h-5) := (hcell (b.h-5) (by omega)).symm
          _ = f2.tape (f2.h-2) := by rw [hidx2]
          _ = true := hw.2.1,
      by
        calc
          b.tape (b.h-4) = f2.tape (b.h-4) := (hcell (b.h-4) (by omega)).symm
          _ = f2.tape (f2.h-1) := by rw [hidx3]
          _ = false := hw.2.2⟩
  have hd2shield : NoLeft4 true true false d2 :=
    noLeft4_right_boundary true true false f2 d2 hd2pos hd2same hboundary2 hf2shield
  have hhead2 : d2.h+2*((n+1)+1)+1 = b.h+(2*n+3:Int) := by
    dsimp [d2,H]
    omega
  have htape2 : evenSweepBResultTape (n+1) d2.tape d2.h =
      evenSweepBResultTape (n+1)
        (setBit (setBit (oddWaveTape n (twoWavePrefixTape b.tape b.h) (b.h-1))
          (b.h-2) true) (b.h-3) false) (b.h-2) := by
    dsimp [d2,f2,b1,H,t1]
    have hidx1 : b.h-1-1 = b.h-2 := by omega
    have hidx2 : b.h-1-2 = b.h-3 := by omega
    rw [hidx1,hidx2]
  have hout : NoLeft4 true true false
      (⟨.B,b.h+(2*n+3:Int),
        evenSweepBResultTape (n+1)
          (setBit (setBit (oddWaveTape n (twoWavePrefixTape b.tape b.h) (b.h-1))
            (b.h-2) true) (b.h-3) false) (b.h-2)⟩ : Conf) := by
    simpa [hhead2,htape2] using
      evenSweepBResultTape_preserves_NoLeft4 (n+1) d2.tape d2.h hd2shield
  have heq : bout =
      (⟨.B,b.h+(2*n+3:Int),
        evenSweepBResultTape (n+1)
          (setBit (setBit (oddWaveTape n (twoWavePrefixTape b.tape b.h) (b.h-1))
            (b.h-2) true) (b.h-3) false) (b.h-2)⟩ : Conf) := by
    cases bout with
    | mk q h t =>
      have hq : q = .B := hBzero.1
      have hh : h = b.h+(2*n+3:Int) := hhead
      have ht : t = evenSweepBResultTape (n+1)
          (setBit (setBit (oddWaveTape n (twoWavePrefixTape b.tape b.h) (b.h-1))
            (b.h-2) true) (b.h-3) false) (b.h-2) := htape
      subst q
      subst h
      subst t
      rfl
  exact ⟨bout,hrun,hreach,hBzero,by rw [heq]; exact hout⟩


/-- A finite synthetic B/0 tape showing that NoLeft4 alone does not imply
    the odd-even boundary hypothesis. This configuration is intentionally
    not asserted to be reachable from the blank root. -/
def oddEvenShieldCounterexampleTape (x : Int) : Bool :=
  decide (x = -6 ∨ x = -5 ∨ x = -3 ∨ x = -1)

def oddEvenShieldCounterexample : Conf :=
  ⟨.B,0,oddEvenShieldCounterexampleTape⟩

def oddEvenShieldCounterexampleSummary (c : Conf) :
    Int × Bool × Bool × Bool × Bool :=
  (c.h,c.tape (-6),c.tape (-5),c.tape (-4),c.tape (-3))

theorem oddEvenShieldCounterexample_NoLeft4 :
    NoLeft4 true true false oddEvenShieldCounterexample := by
  intro x hx hw
  change x+3 < 0 at hx
  have hfirst : x = -6 ∨ x = -5 ∨ x = -3 ∨ x = -1 := by
    simpa [oddEvenShieldCounterexample,oddEvenShieldCounterexampleTape] using hw.1
  rcases hfirst with h | h | h | h
  · subst x
    simp [oddEvenShieldCounterexample,oddEvenShieldCounterexampleTape] at hw
  · subst x
    simp [oddEvenShieldCounterexample,oddEvenShieldCounterexampleTape] at hw
  · omega
  · omega

theorem oddEvenShieldCounterexample_run_summary :
    (run 23 oddEvenShieldCounterexample).map oddEvenShieldCounterexampleSummary =
      some (3,true,true,false,false) := by
  decide

theorem oddEvenShieldCounterexample_run_creates_1100 :
    ∃ c, run 23 oddEvenShieldCounterexample = some c ∧
      c.h = 3 ∧ c.tape (-6) = true ∧ c.tape (-5) = true ∧
      c.tape (-4) = false ∧ c.tape (-3) = false := by
  have hs := oddEvenShieldCounterexample_run_summary
  cases hrun : run 23 oddEvenShieldCounterexample with
  | none => simp [hrun] at hs
  | some c =>
      have hsummary : oddEvenShieldCounterexampleSummary c =
          (3,true,true,false,false) := by
        simpa [hrun] using hs
      have hh : c.h = 3 := congrArg Prod.fst hsummary
      have hrest1 : (c.tape (-6),c.tape (-5),c.tape (-4),c.tape (-3)) =
          (true,true,false,false) := congrArg Prod.snd hsummary
      have h0 : c.tape (-6) = true := congrArg Prod.fst hrest1
      have hrest2 : (c.tape (-5),c.tape (-4),c.tape (-3)) =
          (true,false,false) := congrArg Prod.snd hrest1
      have h1 : c.tape (-5) = true := congrArg Prod.fst hrest2
      have hrest3 : (c.tape (-4),c.tape (-3)) = (false,false) :=
          congrArg Prod.snd hrest2
      have h2 : c.tape (-4) = false := congrArg Prod.fst hrest3
      have h3 : c.tape (-3) = false := congrArg Prod.snd hrest3
      exact ⟨c,rfl,hh,h0,h1,h2,h3⟩

theorem oddEvenShieldCounterexample_run_not_NoLeft4 :
    ∀ c, run 23 oddEvenShieldCounterexample = some c →
      ¬ NoLeft4 true true false c := by
  intro c hrun hshield
  obtain ⟨c',hrun',hh,h0,h1,h2,h3⟩ :=
    oddEvenShieldCounterexample_run_creates_1100
  have hsome : some c = some c' := hrun.symm.trans hrun'
  have heq : c = c' := Option.some.inj hsome
  have hbound : (-6:Int)+3 < c.h := by rw [heq]; omega
  have hword : c.tape (-6) = true ∧ c.tape (-5) = true ∧
      c.tape (-4) = false ∧ c.tape (-3) = false := by
    rw [heq]
    exact ⟨h0,h1,h2,h3⟩
  exact hshield (-6) hbound hword


theorem oddEvenPrefixResultTape_left (n : Nat) (t : Int → Bool) (h x : Int)
    (hx : x ≤ h-4) :
    evenSweepBResultTape (n+1)
      (setBit (setBit (oddWaveTape n (twoWavePrefixTape t h) (h-1))
        (h-2) true) (h-3) false) (h-2) x = t x := by
  have hlt : x < h-2 := by omega
  rw [evenSweepBResultTape_left (n+1)
    (setBit (setBit (oddWaveTape n (twoWavePrefixTape t h) (h-1))
      (h-2) true) (h-3) false) (h-2) x hlt]
  have hne1 : x ≠ h-2 := by omega
  have hne2 : x ≠ h-3 := by omega
  simp only [setBit, if_neg hne1, if_neg hne2]
  rw [oddWaveTape_left n (twoWavePrefixTape t h) (h-1) x (by omega)]
  exact twoWavePrefixTape_left t h x (by omega)

theorem oddEvenPrefixResultTape_at_h_minus_3 (n : Nat) (t : Int → Bool) (h : Int) :
    evenSweepBResultTape (n+1)
      (setBit (setBit (oddWaveTape n (twoWavePrefixTape t h) (h-1))
        (h-2) true) (h-3) false) (h-2) (h-3) = false := by
  have hlt : h-3 < h-2 := by omega
  rw [evenSweepBResultTape_left (n+1)
    (setBit (setBit (oddWaveTape n (twoWavePrefixTape t h) (h-1))
      (h-2) true) (h-3) false) (h-2) (h-3) hlt]
  simp [setBit]

/-- The odd-even return creates a left-of-head 1100 whenever its explicit
    three-cell boundary guard fails. This makes the guard sharp. -/
theorem b0_odd_even_chain_to_b0_exact_bad_boundary
    (b : Conf) (n : Nat)
    (hb : Reach b) (hb0 : BZero b)
    (hleft : b.tape (b.h-1) = true)
    (hzero : b.tape (b.h-2) = false)
    (hone : b.tape (b.h-3) = true)
    (hones : ∀ j : Nat, j < 2*n → b.tape (b.h+1+(j:Int)) = true)
    (hterminal1 : b.tape (b.h+(2*n+1:Int)) = false)
    (hterminal2 : b.tape (b.h+(2*n+2:Int)) = false)
    (hfinal : b.tape (b.h+(2*n+3:Int)) = false)
    (hbad : b.tape (b.h-6) = true ∧ b.tape (b.h-5) = true ∧
      b.tape (b.h-4) = false) :
    ∃ bout : Conf, run (6*n+23) b = some bout ∧
      ¬ NoLeft4 true true false bout := by
  obtain ⟨bout,hrun,hreach,hBzero,hhead,htape⟩ :=
    b0_odd_even_chain_to_b0_exact b n hb hb0 hleft hzero hone hones
      hterminal1 hterminal2 hfinal
  have hcell (x : Int) (hx : x ≤ b.h-4) : bout.tape x = b.tape x := by
    rw [htape]
    exact oddEvenPrefixResultTape_left n b.tape b.h x hx
  have hlast : bout.tape (b.h-3) = false := by
    rw [htape]
    exact oddEvenPrefixResultTape_at_h_minus_3 n b.tape b.h
  have hheadBound : b.h-6+3 < bout.h := by rw [hhead]; omega
  have hword : bout.tape (b.h-6) = true ∧ bout.tape (b.h-5) = true ∧
      bout.tape (b.h-4) = false ∧ bout.tape (b.h-3) = false := by
    exact ⟨(hcell (b.h-6) (by omega)).trans hbad.1,
      (hcell (b.h-5) (by omega)).trans hbad.2.1,
      (hcell (b.h-4) (by omega)).trans hbad.2.2,hlast⟩
  have hword' : bout.tape (b.h-6) = true ∧
      bout.tape ((b.h-6)+1) = true ∧
      bout.tape ((b.h-6)+2) = false ∧
      bout.tape ((b.h-6)+3) = false := by
    have hidx1 : b.h-6+1 = b.h-5 := by omega
    have hidx2 : b.h-6+2 = b.h-4 := by omega
    have hidx3 : b.h-6+3 = b.h-3 := by omega
    simpa [hidx1,hidx2,hidx3] using hword
  exact ⟨bout,hrun,fun hs => hs (b.h-6) hheadBound hword'⟩


/-- Under the input shield and odd-even return hypotheses, the exact output
    is shielded if and only if the three-cell boundary guard holds. -/
theorem b0_odd_even_chain_to_b0_NoLeft4_iff_boundary
    (b : Conf) (n : Nat)
    (hb : Reach b) (hb0 : BZero b)
    (hleft : b.tape (b.h-1) = true)
    (hzero : b.tape (b.h-2) = false)
    (hone : b.tape (b.h-3) = true)
    (hones : ∀ j : Nat, j < 2*n → b.tape (b.h+1+(j:Int)) = true)
    (hterminal1 : b.tape (b.h+(2*n+1:Int)) = false)
    (hterminal2 : b.tape (b.h+(2*n+2:Int)) = false)
    (hfinal : b.tape (b.h+(2*n+3:Int)) = false)
    (hshield : NoLeft4 true true false b) :
    ∃ bout : Conf, run (6*n+23) b = some bout ∧ Reach bout ∧ BZero bout ∧
      (NoLeft4 true true false bout ↔
        ¬(b.tape (b.h-6) = true ∧ b.tape (b.h-5) = true ∧
          b.tape (b.h-4) = false)) := by
  obtain ⟨bout,hrun,hreach,hBzero,hhead,htape⟩ :=
    b0_odd_even_chain_to_b0_exact b n hb hb0 hleft hzero hone hones
      hterminal1 hterminal2 hfinal
  refine ⟨bout,hrun,hreach,hBzero,?_⟩
  constructor
  · intro hout
    have hguard : ¬(b.tape (b.h-6) = true ∧ b.tape (b.h-5) = true ∧
        b.tape (b.h-4) = false) := by
      intro hbad
      obtain ⟨badOut,hrunBad,hnot⟩ :=
        b0_odd_even_chain_to_b0_exact_bad_boundary b n hb hb0 hleft hzero hone
          hones hterminal1 hterminal2 hfinal hbad
      have heq : bout = badOut := Option.some.inj (hrun.symm.trans hrunBad)
      rw [← heq] at hnot
      exact hnot hout
    exact hguard
  · intro hguard
    obtain ⟨safeOut,hrunSafe,hreachSafe,hBzeroSafe,hsafe⟩ :=
      b0_odd_even_chain_to_b0_preserves_NoLeft4 b n hb hb0 hleft hzero hone
        hones hterminal1 hterminal2 hfinal hshield hguard
    have heq : bout = safeOut := Option.some.inj (hrun.symm.trans hrunSafe)
    rw [heq]
    exact hsafe

#print axioms BB6Root119.b0_even_prefix_to_b0_preserves_NoLeft4
#print axioms BB6Root119.b0_odd_even_chain_to_b0_preserves_NoLeft4
#print axioms BB6Root119.oddEvenShieldCounterexample_NoLeft4
#print axioms BB6Root119.oddEvenShieldCounterexample_run_summary
#print axioms BB6Root119.oddEvenShieldCounterexample_run_not_NoLeft4
#print axioms BB6Root119.b0_odd_even_chain_to_b0_exact_bad_boundary
#print axioms BB6Root119.b0_odd_even_chain_to_b0_NoLeft4_iff_boundary

end BB6Root119
