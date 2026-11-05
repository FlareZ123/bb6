import FourthExactTwo
import ResetAncestry
set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace CascadeForkOddDead
open CascadeSweep CascadeAncestry CascadeManyShield
open CascadeAgent10FourthBranch CascadeAgent10Four CascadeAgent10ExactlyTwo

private theorem exp_margin (n : Nat) (hn : 13 ≤ n) :
    523*n+781 ≤ 2^n := by
  have h : ∀k:Nat, 523*(k+13)+781 ≤ 2^(k+13) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+13=k+13+1 by omega, Nat.pow_succ]
      omega
  have he : n=(n-13)+13 := by omega
  rw [he]
  exact h (n-13)

private theorem pow_shift (n : Nat) (hn : 2 ≤ n) :
    2^n = 4*2^(n-2) := by
  have he : n=(n-2)+2 := by omega
  have hp : 2^n=2^((n-2)+2) := congrArg (fun m:Nat=>2^m) he
  rw [Nat.pow_add] at hp
  omega

private theorem odd_linear (n : Nat) (hn : 13 ≤ n)
    (hres : n%54=35 ∨ n%54=46) :
    9*oddPre n + 257*n + 399 = 14*2^n := by
  have h18 : n%18=10 ∨ n%18=17 := by omega
  have hfactor := (odd_factor n (by omega) h18).1
  have hband := odd_band n (by omega) h18
  have hmargin := exp_margin n hn
  have hp := pow_shift n (by omega)
  have hfourth : fourthPred n + 31*n+49 = 4*2^n := by
    dsimp [fourthPred]
    omega
  have hodd : oddPre n + 8*2^(n-2)+(n-2)+5 = 4*d n := by
    dsimp [oddPre]
    omega
  omega

private theorem pow_period_eighteen (n : Nat) : 2^(n+18)%27 = 2^n%27 := by
  rw [Nat.pow_add]
  simp [Nat.mul_mod]

private theorem pow_mod_eighteen (n : Nat) : 2^n%27 = 2^(n%18)%27 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < 18
    · simp [Nat.mod_eq_of_lt hn]
    · have hm : n-18<n := by omega
      have he : n=(n-18)+18 := by omega
      rw [he,pow_period_eighteen]
      rw [ih (n-18) hm]
      have hemod : ((n-18)+18)%18=(n-18)%18 := by omega
      rw [hemod]

private theorem odd_mod_three (n : Nat) (hn : 13 ≤ n)
    (hres : n%54=35 ∨ n%54=46) : oddPre n%3=1 := by
  have hl := odd_linear n hn hres
  have hp := pow_mod_eighteen n
  rcases hres with hr|hr
  · have hn18 : n%18=17 := by omega
    have hn27 : n%27=8 := by omega
    have hP : 2^n%27=14 := by rw [hp,hn18]
    omega
  · have hn18 : n%18=10 := by omega
    have hn27 : n%27=19 := by omega
    have hP : 2^n%27=25 := by rw [hp,hn18]
    omega

def gapHeight (n : Nat) : Nat := 2*oddPre n-2*2^n-(n-2)

private theorem gap_linear (n : Nat) (hn : 13 ≤ n)
    (hres : n%54=35 ∨ n%54=46) :
    gapHeight n + 2*2^n+(n-2)=2*oddPre n ∧
    9*gapHeight n + 523*n+780=10*2^n := by
  have hmargin := exp_margin n hn
  have hv := odd_linear n hn hres
  have hpos : 2*2^n+n-2 ≤ 2*oddPre n := by omega
  have hdef : gapHeight n + 2*2^n+(n-2)=2*oddPre n := by
    dsimp [gapHeight]
    omega
  constructor
  · exact hdef
  · omega

private theorem gap_bounds (n : Nat) (hn : 13 ≤ n)
    (hres : n%54=35 ∨ n%54=46) :
    2^n < gapHeight n ∧ 2*gapHeight n+2 < 3*2^n := by
  have hmargin := exp_margin n hn
  have hl := (gap_linear n hn hres).2
  omega

private theorem gap_mod_three (n : Nat) (hn : 13 ≤ n)
    (hres : n%54=35 ∨ n%54=46) : gapHeight n%3=1 := by
  have hg := (gap_linear n hn hres).1
  have ho := odd_mod_three n hn hres
  rcases hres with hr|hr
  · have hP : 2^n%3=2 := by
      have h18 : n%18=17 := by omega
      have hp := pow_mod_eighteen n
      have hP27 : 2^n%27=14 := by rw [hp,h18]
      omega
    omega
  · have hP : 2^n%3=1 := by
      have h18 : n%18=10 := by omega
      have hp := pow_mod_eighteen n
      have hP27 : 2^n%27=25 := by rw [hp,h18]
      omega
    omega

/-- Any u in (2^n, 3/2*2^n) is in no exact even first-reset image. -/
theorem gap_avoids_even_images (n u : Nat) (_hn : 3 ≤ n)
    (hlo : 2^n < u) (hhi : 2*u+2 < 3*2^n) :
    ∀k, ¬(6*2^k-1 ≤ u ∧ u ≤ 8*2^k-3) := by
  intro k hb
  by_cases hk : k+3 ≤ n
  · have hpow : 2^(k+3) ≤ 2^n := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hk
    have he : 2^(k+3)=8*2^k := by rw [Nat.pow_add]; omega
    rw [he] at hpow
    omega
  · have hnk : n ≤ k+2 := by omega
    have hpow : 2^n ≤ 2^(k+2) := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hnk
    have he : 2^(k+2) = 4*2^k := by rw [Nat.pow_add]; omega
    rw [he] at hpow
    omega

private theorem odd_even_band (n : Nat) (hn : 13≤n)
    (hres : n%54=35 ∨ n%54=46) :
    6*2^(n-2)-1 ≤ oddPre n ∧ oddPre n ≤ 8*2^(n-2)-3 := by
  have hl := odd_linear n hn hres
  have hm := exp_margin n hn
  have hp := pow_shift n (by omega)
  omega

/-- An odd fourth-fork parent in two infinite index classes is excluded
    from the actual reset-root orbit by its single incoming even predecessor,
    which lies inside the dyadic image gap with wrong mod-3 residue. -/
theorem odd_fork_branch_unreachable (n : Nat) (hn : 13 ≤ n)
    (hres : n%54=35 ∨ n%54=46) :
    ¬ReachC (2,0) (oddPre n,0) := by
  intro hr
  have hb := odd_even_band n hn hres
  have hmod : oddPre n%3≠2 := by rw [odd_mod_three n hn hres]; decide
  obtain ⟨h,k,hreach,hl,hu,heq⟩ := reachable_even_reset_parent (oddPre n) hr hmod
  have hk : k=n-2 := even_band_unique (oddPre n) k (n-2) ⟨hl,hu⟩ hb
  have hsource := (gap_linear n hn hres).1
  have hpow := pow_shift n (by omega)
  have hEq : h=gapHeight n := by
    rw [hk] at heq
    omega
  rw [hEq] at hreach
  have hgap := gap_bounds n hn hres
  have hnomod : gapHeight n%3 ≠ 2 := by rw [gap_mod_three n hn hres]; decide
  exact (root_excludes_nonimage (gapHeight n) hnomod
    (gap_avoids_even_images n (gapHeight n) (by omega) hgap.1 hgap.2)) hreach

/-- Entire odd half of the source-authentic fourth fork is unreachable,
    leaving a single genuine-root gate across n=35,46 (mod 54). -/
theorem fatal_iff_even_fifth_parent (n : Nat) (hn : 13 ≤ n)
    (hres : n%54=35 ∨ n%54=46) :
    ReachC (2,0) (fatal n,0) ↔ ReachC (2,0) (evenPre n,0) := by
  have hprior := genuine_fatal_iff_two_parent_roots n (by omega)
    (by rcases hres with hr|hr
        · exact Or.inr (Or.inr (Or.inl hr))
        · exact Or.inr (Or.inr (Or.inr hr)))
  constructor
  · intro hroot
    rcases hprior.mp hroot with hodd|heven
    · exact False.elim ((odd_fork_branch_unreachable n hn hres) hodd)
    · exact heven
  · intro heven
    exact hprior.mpr (Or.inr heven)

#print axioms odd_fork_branch_unreachable
#print axioms fatal_iff_even_fifth_parent
end CascadeForkOddDead
