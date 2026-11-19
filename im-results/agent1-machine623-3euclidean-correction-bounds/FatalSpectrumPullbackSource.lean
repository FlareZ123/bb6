import Agent49ParitySource
import Agent49FastFailureSpectrumSource
import Agent49ExactOddSectorSource
import Agent49ExactEvenSectorSource

namespace BB6.Agent1FatalSpectrumPullback

open BB6.Agent49ParitySource
open BB6.Agent49FastSpectrum
open BB6.Agent49OddSector
open BB6.Agent49EvenSector
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- A member of the exact B-drain failure spectrum must lie beyond the
all-ones safe threshold. -/
theorem fastSpectrum_requires_ones (x b : Nat)
    (hmem : x ∈ fastSpectrum b) :
    3^x ≤ 2*b-1 := by
  have hnone : drainB x b 0 = none :=
    (drain_none_iff_fastSpectrum x b 0).2 hmem
  have hgt : ternaryOnes x < b := by
    by_contra h
    have hb : b ≤ ternaryOnes x := by omega
    obtain ⟨aa,dd,hret⟩ := drainB_safe_ones b x 0 hb
    rw [hret] at hnone
    contradiction
  have hpow := twice_ones_add_one_eq_pow x
  omega

/-- If a successful evaluator call is followed by a fatal B-drain, then
its input first counter is exponentially bounded by its input block count.
This follows by induction over the three recursive evalA digit branches,
including the special a=0, digit-1 return. -/
theorem evalA_success_fatal_exponential (a k m x b r : Nat)
    (heval : evalA a k m = some (x,b,r))
    (hfatal : x ∈ fastSpectrum b) :
    3^a ≤ 2*k+1 := by
  induction a generalizing k m x b r with
  | zero =>
      rw [evalA] at heval
      by_cases h2 : k % 3 = 2
      · simp [h2] at heval
        omega
      · by_cases h0 : k % 3 = 0
        · simp [h2,h0] at heval
        · simp [h2,h0] at heval
          omega
  | succ a ih =>
      rw [evalA] at heval
      by_cases h2 : k % 3 = 2
      · simp [h2] at heval
        rcases heval with ⟨hx,hb,hr⟩
        subst x
        subst b
        subst r
        have hspec := fastSpectrum_requires_ones (a+2) (k/3) hfatal
        have hmod : k = 3*(k/3)+2 := by
          have h := Nat.mod_add_div k 3
          omega
        have hpow : 3^(a+2) = 3^(a+1)*3 := by
          rw [Nat.pow_succ]
        omega
      · simp [h2] at heval
        by_cases h0 : k % 3 = 0
        · simp [h0] at heval
          rcases heval with ⟨hx,hb,hr⟩
          subst x
          subst b
          subst r
          have hspec := fastSpectrum_requires_ones a (k/3) hfatal
          have hmod : k = 3*(k/3) := by
            have h := Nat.mod_add_div k 3
            omega
          have hpow : 3^(a+1) = 3^a*3 := by
            rw [Nat.pow_succ]
          omega
        · simp [h0] at heval
          have hIH := ih (k/3) (m+2*(k/3)+3) x b r heval hfatal
          have hmod : k = 3*(k/3)+1 := by
            have h := Nat.mod_add_div k 3
            omega
          have hpow : 3^(a+1) = 3^a*3 := by
            rw [Nat.pow_succ]
          omega

/-- Exact odd-third fatality, pulled back to a power-of-three condition or
one of the two small near-left gaps. -/
theorem odd_terminal_gap_spectrum (a d : Nat)
    (ha0 : 0<a) (ha : a%2=0) (hd : d%2=1)
    (hhalt : highLevelNext (.D a d)=none) :
    (d+5≤a ∧ 3^(a-d-5)≤2*d+5) ∨
    (a≤d ∧ 3^(d+4-a)≤2*a-3) ∨
    (d<a ∧ a≤d+3) := by
  have hspec := (odd_even_none_iff_two_spectra a d hd ha0 ha).mp hhalt
  rcases hspec with hfar | hnear
  · rcases hfar with ⟨hfar,hmem⟩
    have hpow := fastSpectrum_requires_ones (a-d-5) (d+3) hmem
    exact Or.inl ⟨hfar,by omega⟩
  · rcases hnear with ⟨hnear,hmem⟩
    by_cases hside : a≤d
    · have hpow := fastSpectrum_requires_ones (d+4-a) (a-1) hmem
      exact Or.inr (Or.inl ⟨hside,by omega⟩)
    · exact Or.inr (Or.inr ⟨by omega,hnear⟩)

/-- Exact even-third fatality, including both initial evaluator failure
and a successful evaluator followed by a fatal B-drain. -/
theorem even_terminal_gap_spectrum (a d : Nat)
    (ha0 : 0<a) (ha : a%2=0) (hd : d%2=0)
    (hhalt : highLevelNext (.D a d)=none) :
    (d+3≤a ∧ 3^(a-d-2)≤2*d+3) ∨
    (a=d+2) ∨
    (a≤d ∧ 3^(d+1-a)≤2*a+1) := by
  have hspec := (even_even_none_iff_three_spectra a d ha0 ha hd).mp hhalt
  rcases hspec with hfar | hdiag | hright
  · rcases hfar with ⟨hfar,hmem⟩
    have hpow := fastSpectrum_requires_ones (a-d-2) (d+2) hmem
    exact Or.inl ⟨hfar,by omega⟩
  · exact Or.inr (Or.inl hdiag.1)
  · rcases hright with ⟨hside,hcond⟩
    rcases hcond with hgate | ⟨x,b,m,hEval,hmem⟩
    · have hmod : a % 3^(d+2-a) = ternaryOnes (d+1-a) := by
        rw [ternaryOnes_eq_half]
        exact hgate
      have hrem : ternaryOnes (d+1-a) ≤ a := by
        have hm := Nat.mod_le a (3^(d+2-a))
        rw [hmod] at hm
        exact hm
      have hpow := twice_ones_add_one_eq_pow (d+1-a)
      exact Or.inr (Or.inr ⟨hside,by omega⟩)
    · have hpow := evalA_success_fatal_exponential
        (d+1-a) a (2*a+5) x b m hEval hmem
      exact Or.inr (Or.inr ⟨hside,hpow⟩)

/-- For n≥10, the joint-mass envelope 6*3^n+12*n+28 is below
the next two ternary orders, with room for the +5 in the fatal spectra. -/
theorem mass_envelope_lt_three_power :
    ∀ n : Nat, 10≤n → 6*3^n+12*n+33 < 3^(n+2) := by
  intro n
  induction n with
  | zero =>
      intro hn
      omega
  | succ n ih =>
      intro hn
      have hn0 : 10≤n := by omega
      have hprev := ih hn0
      have hpowL : 3^(n+1) = 3^n*3 := by
        rw [Nat.pow_succ]
      have hpowR : 3^(n+3) = 3^(n+2)*3 := by
        rw [Nat.pow_succ]
      rw [hpowL,hpowR]
      nlinarith

/-- Strict monotonicity of powers of three, in the exponent direction. -/
theorem pow_three_lt_exponent (k n : Nat)
    (h : 3^k < 3^(n+2)) :
    k≤n+1 := by
  by_contra hnot
  have hkn : n+2≤k := by omega
  have hmono : 3^(n+2)≤3^k := by
    gcongr
  omega

/-- With the source joint-mass envelope, a terminal odd-third state has
the branch-sensitive successor-gap bounds used in the pullback note. -/
theorem odd_terminal_gap_bound (a d n : Nat)
    (ha0 : 0<a) (ha : a%2=0) (hd : d%2=1)
    (hhalt : highLevelNext (.D a d)=none)
    (hMass : a+d≤6*3^n+12*n+28) (hn : 10≤n) :
    (d+5≤a ∧ a-d≤n+6) ∨
    (a≤d ∧ d-a≤n-3) ∨
    (d<a ∧ a-d≤3) := by
  have hsum : a+d+5 < 3^(n+2) := by
    have hle : a+d+5≤6*3^n+12*n+33 := by omega
    exact lt_of_le_of_lt hle (mass_envelope_lt_three_power n hn)
  have hspec := odd_terminal_gap_spectrum a d ha0 ha hd hhalt
  rcases hspec with hfar | hnear | hsmall
  · rcases hfar with ⟨hfar,hpow⟩
    have hR : 2*d+5 < 3^(n+2) := by omega
    have hexp := pow_three_lt_exponent (a-d-5) n (lt_of_le_of_lt hpow hR)
    exact Or.inl ⟨hfar,by omega⟩
  · rcases hnear with ⟨hside,hpow⟩
    have hR : 2*a-3 < 3^(n+2) := by omega
    have hexp := pow_three_lt_exponent (d+4-a) n (lt_of_le_of_lt hpow hR)
    exact Or.inr (Or.inl ⟨hside,by omega⟩)
  · exact Or.inr (Or.inr hsmall)

/-- With the source joint-mass envelope, a terminal even-third state has
the branch-sensitive successor-gap bounds used in the pullback note. -/
theorem even_terminal_gap_bound (a d n : Nat)
    (ha0 : 0<a) (ha : a%2=0) (hd : d%2=0)
    (hhalt : highLevelNext (.D a d)=none)
    (hMass : a+d≤6*3^n+12*n+28) (hn : 10≤n) :
    (d+3≤a ∧ a-d≤n+3) ∨
    (a=d+2) ∨
    (a≤d ∧ d-a≤n) := by
  have hsum : a+d+5 < 3^(n+2) := by
    have hle : a+d+5≤6*3^n+12*n+33 := by omega
    exact lt_of_le_of_lt hle (mass_envelope_lt_three_power n hn)
  have hspec := even_terminal_gap_spectrum a d ha0 ha hd hhalt
  rcases hspec with hfar | hdiag | hright
  · rcases hfar with ⟨hfar,hpow⟩
    have hR : 2*d+3 < 3^(n+2) := by omega
    have hexp := pow_three_lt_exponent (a-d-2) n (lt_of_le_of_lt hpow hR)
    exact Or.inl ⟨hfar,by omega⟩
  · exact Or.inr (Or.inl hdiag)
  · rcases hright with ⟨hside,hpow⟩
    have hR : 2*a+1 < 3^(n+2) := by omega
    have hexp := pow_three_lt_exponent (d+1-a) n (lt_of_le_of_lt hpow hR)
    exact Or.inr (Or.inr ⟨hside,by omega⟩)

#print axioms fastSpectrum_requires_ones
#print axioms evalA_success_fatal_exponential
#print axioms odd_terminal_gap_spectrum
#print axioms even_terminal_gap_spectrum
#print axioms odd_terminal_gap_bound
#print axioms even_terminal_gap_bound

end BB6.Agent1FatalSpectrumPullback
