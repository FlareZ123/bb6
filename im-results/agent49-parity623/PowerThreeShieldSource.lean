import Agent49ExactOddSectorSource

/-!
Original-source-connected unbounded power-of-three fatal-spectrum barriers.
The full drain remains exactly the one in the pinned Cryptids source.
No assertion about the entire genuine blank-root orbit is made.
-/
namespace BB6.Agent49PowerThree
open BB6.Agent49FullSpectrum
open BB6.Agent49FastSpectrum
open BB6.Agent49OddSector
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

private theorem div3_bound (x : Nat) : x/3+x%3 ≤ x := by omega

/-- A boundary barrier uniform in the exponent. -/
theorem boundary_bound (p : Nat) :
    ∀ a b r, b+r=3^p → badAll a b = true → a ≤ r/3 + r%3 := by
  induction p with
  | zero =>
      intro a b r hs hb
      have hp : b ≤ 1 := by simpa using (show b ≤ 1 by omega)
      by_cases hzero : b=0
      · simp [badAll, hzero] at hb
      · have hone : b=1 := by omega
        have ha : a=0 := by
          simpa [badAll, hone] using hb
        omega
  | succ p ih =>
      intro a b r hs hb
      have heq : b+r=3*(3^p) := by
        simpa [Nat.pow_succ, Nat.mul_comm] using hs
      by_cases hz : b=0
      · simp [badAll,hz] at hb
      · have hr : r%3 <3 := Nat.mod_lt r (by omega)
        have hm : b%3 <3 := Nat.mod_lt b (by omega)
        by_cases h0 : b%3=0
        · have hrr : r%3=0 := by omega
          have hc : b/3-1+(r/3+1)=3^p := by omega
          have hnext : badAll (a+1) (b/3-1) = true := by
            rw [badAll] at hb
            simpa only [if_neg hz, if_pos h0] using hb
          have hi := ih (a+1) (b/3-1) (r/3+1) hc hnext
          have hd := div3_bound (r/3+1)
          omega
        · by_cases h1 : b%3=1
          · have hrr : r%3=2 := by omega
            by_cases ha : a=0
            · omega
            · have hc : b/3+(r/3+1)=3^p := by omega
              have hnext : badAll (a-1) (b/3) = true := by
                rw [badAll] at hb
                simpa only [if_neg hz, if_neg h0, if_pos h1, if_neg ha] using hb
              have hi := ih (a-1) (b/3) (r/3+1) hc hnext
              have hd := div3_bound (r/3+1)
              omega
          · have h2 : b%3=2 := by omega
            have hrr : r%3=1 := by omega
            by_cases ha : a=0
            · omega
            · have hc : (b/3+1)+(r/3)=3^p := by omega
              have hnext : badAll (a-1) (b/3+1) = true := by
                rw [badAll] at hb
                simpa only [if_neg hz, if_neg h0, if_neg h1, if_neg ha] using hb
              have hi := ih (a-1) (b/3+1) (r/3) hc hnext
              have hd := div3_bound (r/3)
              omega

private theorem bad_zero_3q2 (q : Nat) : badAll 0 (3*q+2) = badAll 0 q := by
  rw [badAll]
  have hdiv : (3*q+2)/3=q := by omega
  simp [hdiv]

private theorem bad_one_3q1 (q : Nat) : badAll 1 (3*q+1) = badAll 0 q := by
  rw [badAll]
  have hdiv : (3*q+1)/3=q := by omega
  simp [hdiv]

private theorem bad_two_3q1 (q : Nat) : badAll 2 (3*q+1) = badAll 1 q := by
  rw [badAll]
  have hdiv : (3*q+1)/3=q := by omega
  simp [hdiv]

private theorem bad_one_3q2 (q : Nat) : badAll 1 (3*q+2) = badAll 0 (q+1) := by
  rw [badAll]
  have hdiv : (3*q+2)/3=q := by omega
  simp [hdiv]

private theorem bad_zero_3q (q : Nat) (hq : 0<q) :
    badAll 0 (3*q) = badAll 1 (q-1) := by
  rw [badAll]
  simp [show 3*q ≠ 0 by omega]

private theorem power_pos (p : Nat) : 0<3^p := by exact Nat.pow_pos (by decide)

theorem zero_left_edge (p : Nat) : badAll 0 (3^p-1) = false := by
  induction p with
  | zero => simp [badAll]
  | succ p ih =>
      have hp := power_pos p
      have ht : 3^(p+1)-1 = 3*(3^p-1)+2 := by
        rw [Nat.pow_succ]
        omega
      rw [ht, bad_zero_3q2]
      exact ih

theorem one_left_two (p : Nat) : badAll 1 (3^p-2) = false := by
  cases p with
  | zero => simp [badAll]
  | succ p =>
      have hp := power_pos p
      have ht : 3^(p+1)-2 = 3*(3^p-1)+1 := by
        rw [Nat.pow_succ]
        omega
      rw [ht, bad_one_3q1]
      exact zero_left_edge p

theorem zero_left_three (p : Nat) : badAll 0 (3^p-3) = false := by
  cases p with
  | zero => simp [badAll]
  | succ p =>
      have hp := power_pos p
      have ht : 3^(p+1)-3 = 3*(3^p-1) := by
        rw [Nat.pow_succ]
        omega
      rw [ht]
      by_cases hx : 3^p=1
      · have pp : p=0 := by
          cases p with
          | zero => rfl
          | succ p =>
              have hpo:=power_pos p
              simp only [Nat.pow_succ] at hx
              omega
        subst p
        simp [badAll]
      · rw [bad_zero_3q (3^p-1) (by omega)]
        have harg : (3^p-1)-1 =3^p-2 := by omega
        rw [harg]
        exact one_left_two p

theorem two_left_five (p : Nat) : badAll 2 (3^p-5)=false := by
  cases p with
  | zero => simp [badAll]
  | succ p =>
      by_cases hs : p=0
      · subst p; simp [badAll]
      · have hp : 2≤3^p := by
          cases p with
          | zero => contradiction
          | succ p =>
              have hpo:=power_pos p
              simp only [Nat.pow_succ]
              omega
        have ht : 3^(p+1)-5 = 3*(3^p-2)+1 := by
          rw [Nat.pow_succ]
          omega
        rw [ht, bad_two_3q1]
        exact one_left_two p

theorem one_left_four (p : Nat) : badAll 1 (3^p-4)=false := by
  cases p with
  | zero => simp [badAll]
  | succ p =>
      by_cases hs : p=0
      · subst p; simp [badAll]
      · have hp : 2≤3^p := by
          cases p with
          | zero => contradiction
          | succ p =>
              have hpo:=power_pos p
              simp only [Nat.pow_succ]
              omega
        have ht : 3^(p+1)-4 = 3*(3^p-2)+2 := by
          rw [Nat.pow_succ]
          omega
        rw [ht, bad_one_3q2]
        have harg : (3^p-2)+1=3^p-1 := by omega
        rw [harg]
        exact zero_left_edge p

/-- The entire anti-diagonal a+b=3^p-1 is B-drain safe, with no parity assumptions. -/
theorem no_fatal_diagonal_one (p a b : Nat) (hs : a+b+1=3^p) :
    badAll a b ≠ true := by
  intro hb
  have hbound := boundary_bound p a b (a+1) (by omega) hb
  have hr : (a+1)%3<3 := Nat.mod_lt _ (by decide)
  by_cases ha0 : a=0
  · have hx : b=3^p-1 := by omega
    have hh := zero_left_edge p
    simp [ha0,hx] at hb
    simp [hh] at hb
  · by_cases ha1 : a=1
    · have hx : b=3^p-2 := by omega
      have hh := one_left_two p
      simp [ha1,hx] at hb
      simp [hh] at hb
    · omega

/-- The entire anti-diagonal a+b=3^p-3 is B-drain safe, with no parity assumptions. -/
theorem no_fatal_diagonal_three (p a b : Nat) (hs : a+b+3=3^p) :
    badAll a b ≠ true := by
  intro hb
  have hbound := boundary_bound p a b (a+3) (by omega) hb
  have hr : (a+3)%3<3 := Nat.mod_lt _ (by decide)
  by_cases ha0 : a=0
  · have hx : b=3^p-3 := by omega
    have hh := zero_left_three p
    simp [ha0,hx] at hb
    simp [hh] at hb
  · by_cases ha1 : a=1
    · have hx : b=3^p-4 := by omega
      have hh := one_left_four p
      simp [ha1,hx] at hb
      simp [hh] at hb
    · by_cases ha2 : a=2
      · have hx : b=3^p-5 := by omega
        have hh := two_left_five p
        simp [ha2,hx] at hb
        simp [hh] at hb
      · omega

private theorem power_ge_two (p : Nat) (hp : 0<p) : 2 ≤ 3^p := by
  cases p with
  | zero => omega
  | succ p =>
      have h : 0<3^p := Nat.pow_pos (by decide : 0<3)
      rw [Nat.pow_succ]
      omega

theorem odd_safe_power (p x : Nat) (hx : x%2=1) :
    badAll x (3^p) ≠ true := by
  intro hf
  have h := boundary_bound p x (3^p) 0 (by omega) hf
  omega

theorem odd_safe_power_minus_two (p x : Nat) (hx : x%2=1) :
    badAll x (3^p-2) ≠ true := by
  intro hf
  by_cases hp : p=0
  · subst p
    simp [badAll] at hf
  · have htwo : 2≤3^p := power_ge_two p (by omega)
    have h := boundary_bound p x (3^p-2) 2 (by omega) hf
    have hone : x=1 := by omega
    have hs := one_left_two p
    rw [hone, hs] at hf
    cases hf

private theorem pow3_odd (p : Nat) : 3^p%2=1 := by
  induction p with
  | zero => decide
  | succ p ih =>
      rw [Nat.pow_succ]
      omega

theorem minus_column_two_spectra (p d : Nat) (hp : 0<p) (hd : d%2=1) :
    (d+5 ≤ 3^p-1 → badAll (3^p-1-d-5) (d+3) ≠ true) ∧
    (3^p-1 ≤ d+3 → badAll (d+4-(3^p-1)) (3^p-1-1) ≠ true) := by
  have hpbig := power_ge_two p hp
  have heven : (3^p-1)%2=0 := by
    have hodd := pow3_odd p
    omega
  constructor
  · intro hfar
    apply no_fatal_diagonal_three p
    omega
  · intro hnear
    have hodd : (d+4-(3^p-1))%2=1 := by omega
    have harg : 3^p-1-1 =3^p-2 := by omega
    rw [harg]
    exact odd_safe_power_minus_two p _ hodd

theorem plus_column_two_spectra (p d : Nat) (hd : d%2=1) :
    (d+5 ≤ 3^p+1 → badAll (3^p+1-d-5) (d+3) ≠ true) ∧
    (3^p+1 ≤ d+3 → badAll (d+4-(3^p+1)) (3^p+1-1) ≠ true) := by
  have hpow := power_pos p
  have heven : (3^p+1)%2=0 := by
    have hodd := pow3_odd p
    omega
  constructor
  · intro hfar
    apply no_fatal_diagonal_one p
    omega
  · intro hnear
    have hodd : (d+4-(3^p+1))%2=1 := by omega
    have harg : 3^p+1-1 =3^p := by omega
    rw [harg]
    exact odd_safe_power p _ hodd

/-- Original highLevelNext, all odd d and positive 3^p-1 first-counter columns. -/
theorem minus_column_original_safe (p d : Nat) (hp : 0<p) (hd : d%2=1) :
    highLevelNext (.D (3^p-1) d) ≠ none := by
  have hbig := power_ge_two p hp
  have ha : 0<3^p-1 := by omega
  have heven : (3^p-1)%2=0 := by
    have hodd := pow3_odd p
    omega
  intro hnone
  have hgate := (odd_even_none_iff_two_spectra (3^p-1) d hd ha heven).1 hnone
  rcases hgate with ⟨hfar, hmem⟩ | ⟨hnear, hmem⟩
  · have hbad := (fastSpectrum_correct (d+3) (3^p-1-d-5)).1 hmem
    exact (minus_column_two_spectra p d hp hd).1 hfar hbad
  · have hbad := (fastSpectrum_correct (3^p-1-1) (d+4-(3^p-1))).1 hmem
    exact (minus_column_two_spectra p d hp hd).2 hnear hbad

/-- Original highLevelNext, all odd d and 3^p+1 first-counter columns. -/
theorem plus_column_original_safe (p d : Nat) (hd : d%2=1) :
    highLevelNext (.D (3^p+1) d) ≠ none := by
  have ha : 0<3^p+1 := by
    have hpos := power_pos p
    omega
  have heven : (3^p+1)%2=0 := by
    have hodd := pow3_odd p
    omega
  intro hnone
  have hgate := (odd_even_none_iff_two_spectra (3^p+1) d hd ha heven).1 hnone
  rcases hgate with ⟨hfar, hmem⟩ | ⟨hnear, hmem⟩
  · have hbad := (fastSpectrum_correct (d+3) (3^p+1-d-5)).1 hmem
    exact (plus_column_two_spectra p d hd).1 hfar hbad
  · have hbad := (fastSpectrum_correct (3^p+1-1) (d+4-(3^p+1))).1 hmem
    exact (plus_column_two_spectra p d hd).2 hnear hbad

/-- Direct exact original-drain formulation of the two anti-diagonals. -/
theorem original_drain_diagonal_one (p a b d : Nat) (h : a+b+1=3^p) :
    drainB a b d ≠ none := by
  intro hnone
  exact no_fatal_diagonal_one p a b h ((drain_none_iff_badAll a b d).1 hnone)

theorem original_drain_diagonal_three (p a b d : Nat) (h : a+b+3=3^p) :
    drainB a b d ≠ none := by
  intro hnone
  exact no_fatal_diagonal_three p a b h ((drain_none_iff_badAll a b d).1 hnone)

/-- Positive power-three-minus-one columns are even and of last ternary digit two. -/
private theorem pow3_minus_even (q : Nat) : (3^(q+1)-1)%2=0 := by
  have hp := pow3_odd (q+1)
  omega

private theorem pow3_minus_mod3 (q : Nat) : (3^(q+1)-1)%3=2 := by
  have hp := power_pos q
  rw [Nat.pow_succ]
  omega

private theorem pow3_minus_div3 (q : Nat) : (3^(q+1)-1)/3 +1 =3^q := by
  have hp := power_pos q
  rw [Nat.pow_succ]
  omega

/-- The entire power-three-minus-one first-counter column survives for even d. -/
theorem minus_column_even_safe (q d : Nat) (hd : d%2=0) :
    highLevelNext (.D (3^(q+1)-1) d) ≠ none := by
  let a := 3^(q+1)-1
  have ha0 : a≠0 := by
    dsimp [a]
    have hp := power_pos q
    rw [Nat.pow_succ]
    omega
  have haeven : a%2=0 := pow3_minus_even q
  have hanear : ¬(d%2=1 ∧ a≥d+5) := by omega
  intro hh
  have hh' := hh
  change highLevelNext (.D a d) = none at hh'
  simp only [highLevelNext, if_neg ha0, if_neg hanear] at hh'
  by_cases hfar : d+3≤a
  · have hc : d%2=0 ∧ a≥d+3 := ⟨hd,hfar⟩
    simp only [if_pos hc] at hh'
    have hb := (drain_none_iff_badAll (a-d-2) (d+2) 2).1 hh'
    exact no_fatal_diagonal_one (q+1) (a-d-2) (d+2) (by dsimp [a]; omega) hb
  · have hc : ¬(d%2=0 ∧ a≥d+3) := by omega
    simp only [if_neg hc] at hh'
    have hae : a%2≠1 := by omega
    simp only [if_neg hae] at hh'
    by_cases hdiag : a=d+2
    · simp only [if_pos hdiag] at hh'
      have hb := (drain_none_iff_badAll 0 a 2).1 hh'
      have hedge : badAll 0 a = false := by simpa only [a] using zero_left_edge (q+1)
      rw [hedge] at hb
      cases hb
    · simp only [if_neg hdiag] at hh'
      have hodd : d%2≠1 := by omega
      simp only [if_neg hodd] at hh'
      have hmod : a%3=2 := pow3_minus_mod3 q
      have heval : evalA (d+1-a) a (2*a+5) =
          some (d+1-a+1,a/3,2*a+5) := by
        rw [evalA]
        simp only [if_pos hmod]
      rw [heval] at hh'
      simp only [Option.bind_some] at hh'
      have hb := (drain_none_iff_badAll (d+1-a+1) (a/3) (2*a+5)).1 hh'
      have hdiv : a/3+1=3^q := pow3_minus_div3 q
      have hbound := boundary_bound q (d+1-a+1) (a/3) 1 (by omega) hb
      omega

/-- Original high-level #623 one-step safety for every d, with no parity restriction. -/
theorem minus_column_all_third_safe (p d : Nat) (hp : 0<p) :
    highLevelNext (.D (3^p-1) d) ≠ none := by
  cases p with
  | zero => omega
  | succ q =>
      by_cases hd : d%2=1
      · exact minus_column_original_safe (q+1) d (by omega) hd
      · have he : d%2=0 := by omega
        exact minus_column_even_safe q d he

#print axioms minus_column_even_safe
#print axioms minus_column_all_third_safe

#print axioms boundary_bound
#print axioms original_drain_diagonal_one
#print axioms original_drain_diagonal_three
#print axioms minus_column_original_safe
#print axioms plus_column_original_safe
end BB6.Agent49PowerThree
