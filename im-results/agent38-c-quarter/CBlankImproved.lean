import CQuarter
namespace BB6Agent38

theorem rank_step_mono (s t : S) (h : nextC s = some t) : rank s ≤ rank t := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp only [nextC,Option.some.injEq] at h; subst t; simp only [rank]; omega
    · rcases k with _|k
      · simp only [nextC,Option.some.injEq] at h; subst t; simp only [rank]; omega
      · simp only [nextC,Option.some.injEq] at h; subst t; simp only [rank]; omega
    · simp only [nextC,Option.some.injEq] at h; subst t; simp only [rank]; omega
  · simp only [nextC,Option.some.injEq] at h; subst t; simp only [rank]; omega
  · simp [nextC] at h
  · simp only [nextC,Option.some.injEq] at h; subst t; simp only [rank]; omega
  · rcases a with _|a
    · by_cases hk : k%2=0
      · simp only [nextC,hk,↓reduceIte,Option.some.injEq] at h
        subst t; simp only [rank]; omega
      · simp only [nextC,hk,↓reduceIte,Option.some.injEq] at h
        subst t; simp only [rank]; omega
    · simp only [nextC,Option.some.injEq] at h
      subst t; simp only [rank]; omega

theorem strong_jump3 (s t:S) (hr:rank t=rank s+3) (h6:6≤rank s) :
    energy s+16≤energy t := by
  have hp:=potential_le_rank t
  unfold energy
  rw [hr] at hp ⊢
  simp only [Nat.add_mul,Nat.mul_add]
  omega

/-- Extra progress of four energy units for each additional rank unit, on
    the actual blank orbit (all rank >= 6). -/
theorem strong_step (s t : S) (h : nextC s = some t) (h6 : 6 ≤ rank s) :
    energy s+4*rank t+4 ≤ energy t+4*rank s := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp only [nextC,Option.some.injEq] at h
      subst t
      simp only [energy,rank,potential, Nat.add_mul,Nat.mul_add] at *
      omega
    · rcases k with _|k
      · simp only [nextC,Option.some.injEq] at h
        subst t
        simp only [energy,rank,potential, Nat.add_mul,Nat.mul_add] at *
        omega
      · simp only [nextC,Option.some.injEq] at h
        subst t
        simp only [energy,rank,potential, Nat.add_mul,Nat.mul_add] at *
        omega
    · simp only [nextC,Option.some.injEq] at h
      subst t
      simp only [energy,rank,potential, Nat.add_mul,Nat.mul_add] at *
      omega
  · simp only [nextC,Option.some.injEq] at h
    subst t
    simp only [energy,rank,potential, Nat.add_mul,Nat.mul_add] at *
    omega
  · simp [nextC] at h
  · simp only [nextC,Option.some.injEq] at h
    subst t
    simp only [energy,rank,potential, Nat.add_mul,Nat.mul_add] at *
    omega
  · rcases a with _|a
    · by_cases hk : k%2=0
      · simp only [nextC,hk,↓reduceIte,Option.some.injEq] at h
        subst t
        have hr : rank (4*(k/2)+2,2,d+1) = rank (0,k,d+1+1+1+1)+3 := by
          simp only [rank]
          omega
        have hs := strong_jump3 (0,k,d+1+1+1+1) (4*(k/2)+2,2,d+1) hr h6
        omega
      · simp only [nextC,hk,↓reduceIte,Option.some.injEq] at h
        subst t
        have hd : d+1+1+1+1=d+4 := by omega
        simp only [hd] at h6 ⊢
        have hr : rank (4*(k/2)+5,0,d+4) = rank (0,k,d+4)+3 := by
          simp only [rank]
          omega
        have hs := strong_jump3 (0,k,d+4) (4*(k/2)+5,0,d+4) hr h6
        omega
    · simp only [nextC,Option.some.injEq] at h
      subst t
      simp only [energy,rank,potential, Nat.add_mul,Nat.mul_add] at *
      omega

theorem strong_run (n : Nat) (s t : S) (h : run n (some s) = some t)
    (h6 : 6 ≤ rank s) :
    energy s+4*rank t+4*n ≤ energy t+4*rank s := by
  induction n generalizing s t with
  | zero =>
      have he : s=t := by simpa [run] using h
      subst t
      omega
  | succ n ih =>
      cases hs : nextC s with
      | none => simp [run,hs,run_none] at h
      | some u =>
          have ht : run n (some u) = some t := by simpa [run,hs] using h
          have hu : 6 ≤ rank u := by
            have hm := rank_step_mono s u hs
            omega
          have hfirst := strong_step s u hs h6
          have htail := ih u t ht hu
          omega

/-- Stronger explicit target bound for the real Machine C blank entry. -/
theorem blank_thin_cutoff (j n : Nat)
    (h : run n (some (5,0,1)) = some (0,2*j,4*j+10)) :
    4*n + 32*j + 46 ≤
      (8*j+10)*(8*j+11)-2*(4*j+10) := by
  have hs := strong_run n (5,0,1) (0,2*j,4*j+10) h (by decide)
  have hr : rank (0,2*j,4*j+10) = 8*j+10 := by
    simp only [rank]
    omega
  have hp : potential (0,2*j,4*j+10) = 4*j+10 := by simp [potential]
  have he : energy (5,0,1) = 30 := by decide
  have hs0 : rank (5,0,1) = 6 := by decide
  rw [he] at hs
  simp only [energy,hr,hp,hs0] at hs
  have hadd : 8*j+10+1=8*j+11 := by omega
  rw [hadd] at hs
  omega

/-- Explicit tightened Machine C blank-orbit target-search budget. -/
theorem blank_thin_cutoff_clean (j n : Nat)
    (h : run n (some (5,0,1)) = some (0,2*j,4*j+10)) :
    n ≤ 16*j*(j+2)+11 := by
  have hb := blank_thin_cutoff j n h
  have hprod : (8*j)*(8*j)=4*((16*j)*j) := by
    calc
      (8*j)*(8*j) = (8*8)*(j*j) := by ac_rfl
      _ = (4*16)*(j*j) := rfl
      _ = 4*((16*j)*j) := by ac_rfl
  have hpoly : (8*j+10)*(8*j+11)-2*(4*j+10) =
      4*(16*j*(j+2)+11)+32*j+46 := by
    have he : (8*j+10)*(8*j+11) =
        (4*(16*j*(j+2)+11)+32*j+46)+2*(4*j+10) := by
      simp only [Nat.mul_add,Nat.add_mul]
      rw [hprod]
      omega
    omega
  rw [hpoly] at hb
  omega

#print axioms strong_step
#print axioms strong_run
#print axioms blank_thin_cutoff
#print axioms blank_thin_cutoff_clean
end BB6Agent38
