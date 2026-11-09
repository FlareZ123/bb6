import Agent49PowerThreeShieldSource

/-!
Complete original-source one-step halting classification on every
power-of-three-plus-one first-counter column. The root D(0,7) remains open.
No substitute simulator, sorry, custom axioms or finite cutoff.
-/
namespace BB6.Agent49PlusComplete
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49FullSpectrum
open BB6.Agent49PowerThree

private theorem power_pos (p : Nat) : 0 < 3^p :=
  Nat.pow_pos (by decide)

private theorem pow3_odd (p : Nat) : 3^p%2=1 := by
  induction p with
  | zero => decide
  | succ p ih =>
      rw [Nat.pow_succ]
      omega

private theorem div3_bound (x : Nat) : x/3+x%3 ≤ x := by omega

/-- Far-left even-third part of every plus-one column is universally safe. -/
theorem plus_far_even_safe (p d : Nat) (hd : d%2=0)
    (hfar : d+3≤3^p+1) :
    highLevelNext (.D (3^p+1) d) ≠ none := by
  let a := 3^p+1
  have ha0 : a≠0 := by
    dsimp [a]
    have hp:=power_pos p
    omega
  have heven : a%2=0 := by
    have hodd:=pow3_odd p
    dsimp [a]
    omega
  have hnotodd : ¬(d%2=1 ∧ a≥d+5) := by omega
  intro hh
  have hh' := hh
  change highLevelNext (.D a d) = none at hh'
  simp only [highLevelNext, if_neg ha0, if_neg hnotodd] at hh'
  have hcase : d%2=0 ∧ a≥d+3 := ⟨hd,hfar⟩
  simp only [if_pos hcase] at hh'
  have hb := (drain_none_iff_badAll (a-d-2) (d+2) 2).1 hh'
  have hx : 2≤a-d-2 := by omega
  have hroot : (d+2) + ((a-d-2)-1) = 3^p := by dsimp [a]; omega
  have hbound := boundary_bound p (a-d-2) (d+2) ((a-d-2)-1) hroot hb
  have hdiv := div3_bound ((a-d-2)-1)
  omega

/-- The power-plus diagonal d=a-2 is a genuine one-step fatal input for p>=1. -/
theorem plus_diag_halts (q : Nat) :
    highLevelNext (.D (3^(q+1)+1) (3^(q+1)-1)) = none := by
  let a := 3^(q+1)+1
  let d := 3^(q+1)-1
  have hpow : 0<3^q := power_pos q
  have ha0 : a≠0 := by dsimp [a]; omega
  have hdeven : d%2=0 := by
    have ho := pow3_odd (q+1)
    dsimp [d]
    omega
  have heq : a=d+2 := by dsimp [a,d]; omega
  have hnotodd : ¬(d%2=1 ∧ a≥d+5) := by omega
  have hnotfar : ¬(d%2=0 ∧ a≥d+3) := by omega
  have haeven : a%2≠1 := by
    have ho := pow3_odd (q+1)
    dsimp [a]
    omega
  have hmod : a%3=1 := by dsimp [a]; rw [Nat.pow_succ]; omega
  have hb : badAll 0 a = true := by
    rw [badAll]
    simp [ha0, hmod]
  have hnone := (drain_none_iff_badAll 0 a 2).2 hb
  change highLevelNext (.D a d) = none
  simp only [highLevelNext, if_neg ha0, if_neg hnotodd, if_neg hnotfar,
    if_neg haeven, if_pos heq]
  exact hnone

/-- The additional fatal contact at d=a is genuine for p>=2. -/
theorem plus_equal_halts (q : Nat) :
    highLevelNext (.D (3^(q+2)+1) (3^(q+2)+1)) = none := by
  let a := 3^(q+2)+1
  let d := a
  have hpow : 0<3^q := power_pos q
  have ha0 : a≠0 := by
    dsimp [a]
    have hp := power_pos (q+2)
    omega
  have hdeven : d%2=0 := by
    have ho := pow3_odd (q+2)
    dsimp [d,a]
    omega
  have hnotodd : ¬(d%2=1 ∧ a≥d+5) := by omega
  have hnotfar : ¬(d%2=0 ∧ a≥d+3) := by omega
  have haeven : a%2≠1 := by
    have ho := pow3_odd (q+2)
    dsimp [a]
    omega
  have hnotdiag : a≠d+2 := by omega
  have hnotdodd : d%2≠1 := by omega
  have hmod : a%3=1 := by
    dsimp [a]
    rw [show q+2=(q+1)+1 by omega, Nat.pow_succ]
    have hp:=power_pos (q+1)
    omega
  have hdiv : a/3 = 3^(q+1) := by
    dsimp [a]
    rw [show q+2=(q+1)+1 by omega, Nat.pow_succ]
    have hp:=power_pos (q+1)
    omega
  have hinner : (a/3)%3=0 := by
    rw [hdiv, Nat.pow_succ]
    omega
  have heval : evalA (d+1-a) a (2*a+5) = none := by
    have hdelta : d+1-a=1 := by omega
    rw [hdelta, evalA]
    simp only [if_neg (by omega : a%3 ≠ 2), if_neg (by omega : (1:Nat)≠0),
      if_neg (by omega : a%3 ≠ 0)]
    have hsub : 1-1=0 := by omega
    rw [hsub,evalA]
    simp [hinner]
  change highLevelNext (.D a d) = none
  simp only [highLevelNext, if_neg ha0, if_neg hnotodd, if_neg hnotfar,
    if_neg haeven, if_neg hnotdiag, if_neg hnotdodd]
  rw [heval]
  rfl

/-- Two-digit exact source evaluator when the digits are one then zero. -/
theorem evalA_two_digit (n k m : Nat) (hn : 2≤n)
    (hk1 : k%3=1) (hk0 : (k/3)%3=0) :
    evalA n k m = some (n-2,(k/3)/3,m+2*(k/3)+5) := by
  rw [evalA]
  have hn0 : n ≠ 0 := by omega
  have hk2 : k%3≠2 := by omega
  have hkzero : k%3≠0 := by omega
  simp only [if_neg hk2, if_neg hn0, if_neg hkzero]
  rw [evalA]
  have hn1 : n-1≠0 := by omega
  have hkdiv2 : (k/3)%3≠2 := by omega
  simp only [if_neg hkdiv2, if_neg hn1, if_pos hk0]
  congr 1 <;> omega

/-- The finite low-exponent r=4 branch has an exact three-digit evaluator. -/
theorem evalA_four_high (n m : Nat) (hn : 3≤n) :
    evalA n 4 m = some (n-3,0,m+10) := by
  rw [evalA]
  have hn0 : n≠0 := by omega
  simp only [show 4%3≠2 by decide, if_neg, if_neg hn0,
    show 4%3≠0 by decide]
  have h1 : 4/3=1 := by decide
  rw [h1]
  rw [evalA]
  have hn1 : n-1≠0 := by omega
  simp only [show 1%3≠2 by decide, if_neg, if_neg hn1,
    show 1%3≠0 by decide]
  have h2 : 1/3=0 := by decide
  rw [h2]
  rw [evalA]
  have hn2 : n-1-1≠0 := by omega
  simp only [show 0%3≠2 by decide, if_neg, if_neg hn2,
    show 0%3=0 by decide, if_pos]
  congr 1 <;> omega

/-- Every sufficiently high even third counter is safe on a 3^p+1 column, p>=2. -/
theorem plus_near_high_even_safe (q d : Nat) (hd : d%2=0)
    (hnear : 3^(q+2)+1+2 ≤ d) :
    highLevelNext (.D (3^(q+2)+1) d) ≠ none := by
  let a := 3^(q+2)+1
  have hpos : 0<3^(q+2) := power_pos _
  have ha0 : a≠0 := by dsimp [a]; omega
  have haeven : a%2=0 := by
    have ho := pow3_odd (q+2)
    dsimp [a]
    omega
  have hnotodd : ¬(d%2=1 ∧ a≥d+5) := by omega
  have hnotfar : ¬(d%2=0 ∧ a≥d+3) := by omega
  have haodd : a%2≠1 := by omega
  have hnotdiag : a≠d+2 := by omega
  have hnotdodd : d%2≠1 := by omega
  have hk1 : a%3=1 := by
    dsimp [a]
    rw [show q+2=(q+1)+1 by omega, Nat.pow_succ]
    have ho := power_pos (q+1)
    omega
  have hdiv : a/3=3^(q+1) := by
    dsimp [a]
    rw [show q+2=(q+1)+1 by omega, Nat.pow_succ]
    have ho := power_pos (q+1)
    omega
  have hk0 : (a/3)%3=0 := by
    rw [hdiv, Nat.pow_succ]
    omega
  have hbb : (a/3)/3=3^q := by
    rw [hdiv, Nat.pow_succ]
    omega
  have hn : 2≤d+1-a := by omega
  have hev := evalA_two_digit (d+1-a) a (2*a+5) hn hk1 hk0
  intro hh
  have hh' := hh
  change highLevelNext (.D a d)=none at hh'
  simp only [highLevelNext, if_neg ha0, if_neg hnotodd, if_neg hnotfar,
    if_neg haodd, if_neg hnotdiag, if_neg hnotdodd] at hh'
  rw [hev] at hh'
  simp only [Option.bind_some] at hh'
  have hb := (drain_none_iff_badAll (d+1-a-2) ((a/3)/3)
    (2*a+5+2*(a/3)+5)).1 hh'
  have hbound := boundary_bound q (d+1-a-2) ((a/3)/3) 0 (by omega) hb
  omega

theorem plus_four_near_even_safe (d : Nat) (hd : d%2=0) (hnear : 4≤d) :
    highLevelNext (.D 4 d) ≠ none := by
  by_cases hd4 : d=4
  · subst d
    decide +kernel
  · have hbig : 6≤d := by omega
    have hnotodd : ¬(d%2=1 ∧ (4:Nat)≥d+5) := by omega
    have hnotfar : ¬(d%2=0 ∧ (4:Nat)≥d+3) := by omega
    have hnotdiag : (4:Nat)≠d+2 := by omega
    have hnotdodd : d%2≠1 := by omega
    have hnv : 3≤d+1-4 := by omega
    have hev := evalA_four_high (d+1-4) 13 hnv
    intro hh
    simp only [highLevelNext, if_neg (by decide : (4:Nat)≠0),
      if_neg hnotodd, if_neg hnotfar, if_neg (by decide : (4:Nat)%2≠1),
      if_neg hnotdiag, if_neg hnotdodd] at hh
    rw [hev] at hh
    simp only [Option.bind_some] at hh
    rw [drainB] at hh
    simp at hh

theorem plus_two_even_safe (d : Nat) (hd : d%2=0) :
    highLevelNext (.D 2 d) ≠ none := by
  by_cases hz : d=0
  · subst d
    decide +kernel
  · have hlarge : 2≤d := by omega
    have hnotodd : ¬(d%2=1 ∧ (2:Nat)≥d+5) := by omega
    have hnotfar : ¬(d%2=0 ∧ (2:Nat)≥d+3) := by omega
    have hnotdiag : (2:Nat)≠d+2 := by omega
    have hnotdodd : d%2≠1 := by omega
    have hev : evalA (d+1-2) 2 9 = some (d+1-2+1, 0, 9) := by
      rw [evalA]
      simp
    intro hh
    simp only [highLevelNext, if_neg (by decide : (2:Nat)≠0),
      if_neg hnotodd, if_neg hnotfar, if_neg (by decide : (2:Nat)%2≠1),
      if_neg hnotdiag, if_neg hnotdodd] at hh
    rw [hev] at hh
    simp only [Option.bind_some] at hh
    rw [drainB] at hh
    simp at hh

/-- Exact one-step failure criterion on every large 3^p+1 column, p>=2. -/
theorem plus_ge_two_complete (q d : Nat) :
    (highLevelNext (.D (3^(q+2)+1) d)=none) ↔
      (d=3^(q+2)-1 ∨ d=3^(q+2)+1) := by
  let a := 3^(q+2)+1
  have hp : 0<3^(q+2) := power_pos _
  have hae : a%2=0 := by
    have ho:=pow3_odd (q+2)
    dsimp [a]
    omega
  constructor
  · intro hh
    by_cases hodd : d%2=1
    · exact False.elim ((plus_column_original_safe (q+2) d hodd) hh)
    · have hd : d%2=0 := by omega
      by_cases hfar : d+3≤a
      · exact False.elim ((plus_far_even_safe (q+2) d hd (by dsimp [a] at hfar; exact hfar)) hh)
      · by_cases hdiag : d=3^(q+2)-1
        · exact Or.inl hdiag
        · by_cases heq : d=3^(q+2)+1
          · exact Or.inr heq
          · have hnear : 3^(q+2)+1+2≤d := by
              dsimp [a] at hfar
              omega
            exact False.elim ((plus_near_high_even_safe q d hd hnear) hh)
  · rintro (hdiag | heq)
    · rw [hdiag]
      exact plus_diag_halts (q+1)
    · rw [heq]
      exact plus_equal_halts q

/-- Exact one-step failure criterion at exponent one. -/
theorem plus_four_complete (d : Nat) :
    highLevelNext (.D 4 d)=none ↔ d=2 := by
  constructor
  · intro hh
    by_cases hodd : d%2=1
    · have he := plus_column_original_safe 1 d hodd
      exact False.elim (he hh)
    · have hd : d%2=0 := by omega
      by_cases hfar : d+3≤4
      · exact False.elim ((plus_far_even_safe 1 d hd hfar) hh)
      · by_cases heq : d=2
        · exact heq
        · have hnear : 4≤d := by omega
          exact False.elim ((plus_four_near_even_safe d hd hnear) hh)
  · intro heq
    subst d
    exact plus_diag_halts 0

/-- Exponent zero gives the everywhere-safe column a=2. -/
theorem plus_two_all_safe (d : Nat) : highLevelNext (.D 2 d) ≠ none := by
  by_cases hd : d%2=1
  · simpa using plus_column_original_safe 0 d hd
  · exact plus_two_even_safe d (by omega)

#print axioms plus_ge_two_complete
#print axioms plus_four_complete
#print axioms plus_two_all_safe
end BB6.Agent49PlusComplete
