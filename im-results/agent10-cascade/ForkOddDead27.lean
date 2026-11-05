import ForkOddDead
set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace CascadeForkOddDead27
open CascadeResetInverse CascadeSweep CascadeUniformFatal CascadeManyShield
open CascadeAgent10FourthBranch CascadeAgent10Four CascadeAgent10ExactlyTwo CascadeForkOddDead

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

private theorem pow_shift (n : Nat) (hn : 2≤n) :
    2^n = 4*2^(n-2) := by
  have he : n=(n-2)+2 := by omega
  have hp : 2^n=2^((n-2)+2) := congrArg (fun m:Nat=>2^m) he
  rw [Nat.pow_add] at hp
  omega

private theorem pow_shift_one (n : Nat) (hn : 1≤n) :
    2^n = 2*2^(n-1) := by
  have he : n=(n-1)+1 := by omega
  have hp : 2^n=2^((n-1)+1) := congrArg (fun m:Nat=>2^m) he
  rw [Nat.pow_succ] at hp
  omega

private theorem odd_linear (n : Nat) (hn : 13 ≤ n)
    (hres : n%54=17 ∨ n%54=28 ∨ n%54=35 ∨ n%54=46) :
    9*oddPre n+257*n+399=14*2^n := by
  have h18 : n%18=10 ∨ n%18=17 := by omega
  have hfactor := (odd_factor n (by omega) h18).1
  have hband := odd_band n (by omega) h18
  have hmargin := exp_margin n hn
  have hp := pow_shift n (by omega)
  have hfourth : fourthPred n +31*n+49 =4*2^n := by
    dsimp [fourthPred]
    omega
  have hodd : oddPre n+8*2^(n-2)+(n-2)+5=4*d n := by
    dsimp [oddPre]
    omega
  omega

private theorem gap_linear (n:Nat) (hn:13≤n)
    (hres : n%54=17 ∨ n%54=28 ∨ n%54=35 ∨ n%54=46) :
    gapHeight n + 2*2^n+(n-2)=2*oddPre n ∧
    9*gapHeight n+523*n+780=10*2^n := by
  have hm := exp_margin n hn
  have hv := odd_linear n hn hres
  have hpos : 2*2^n+n-2 ≤ 2*oddPre n := by omega
  have heq : gapHeight n +2*2^n+(n-2)=2*oddPre n := by
    dsimp [gapHeight]
    omega
  constructor
  · exact heq
  · omega

private theorem gap_bounds (n:Nat) (hn:13≤n)
    (hres : n%54=17 ∨ n%54=28 ∨ n%54=35 ∨ n%54=46) :
    2^n < gapHeight n ∧ 2*gapHeight n+2 < 3*2^n := by
  have hm := exp_margin n hn
  have hl := (gap_linear n hn hres).2
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

private theorem gap_residue (n:Nat) (hn:13≤n)
    (hres : n%54=17 ∨ n%54=28 ∨ n%54=35 ∨ n%54=46) :
    gapHeight n%3≠2 := by
  have hg := (gap_linear n hn hres).1
  have hv := odd_linear n hn hres
  have hp := pow_mod_eighteen n
  rcases hres with hr|hr|hr|hr
  · have h18 : n%18=17 := by omega
    have h27 : n%27=17 := by omega
    have hP : 2^n%27=14 := by rw [hp,h18]
    omega
  · have h18 : n%18=10 := by omega
    have h27 : n%27=1 := by omega
    have hP : 2^n%27=25 := by rw [hp,h18]
    omega
  · have h18 : n%18=17 := by omega
    have h27 : n%27=8 := by omega
    have hP : 2^n%27=14 := by rw [hp,h18]
    omega
  · have h18 : n%18=10 := by omega
    have h27 : n%27=19 := by omega
    have hP : 2^n%27=25 := by rw [hp,h18]
    omega

private theorem odd_even_band (n:Nat) (hn:13≤n)
    (hres : n%54=17 ∨ n%54=28 ∨ n%54=35 ∨ n%54=46) :
    6*2^(n-2)-1 ≤ oddPre n ∧ oddPre n ≤ 8*2^(n-2)-3 := by
  have hl := odd_linear n hn hres
  have hm := exp_margin n hn
  have hp := pow_shift n (by omega)
  omega

private theorem odd_near_top (n:Nat) (hn:13≤n)
    (hres : n%54=17 ∨ n%54=28 ∨ n%54=35 ∨ n%54=46) :
    3*2^(n-1) ≤ oddPre n ∧ oddPre n ≤ 4*2^(n-1) := by
  have hl := odd_linear n hn hres
  have hm := exp_margin n hn
  have hp := pow_shift_one n (by omega)
  omega

/-- Odd-valuation image bands are disjoint from the dyadic middle gap. -/
theorem gap_avoids_odd_images (n q:Nat) (hl:2^n<q)
    (hu:2*q+2<3*2^n) :
    ∀k, ¬(6*2^k+1 ≤ q ∧ q ≤ 8*2^k-1) := by
  intro k ⟨hlo,hhi⟩
  by_cases hk:k+3≤n
  · have hp : 2^(k+3)≤2^n := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hk
    have he : 2^(k+3)=8*2^k := by rw [Nat.pow_add];omega
    rw [he] at hp
    omega
  · have hnk : n≤k+2 := by omega
    have hp : 2^n≤2^(k+2) := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hnk
    have he : 2^(k+2)=4*2^k := by rw [Nat.pow_add];omega
    rw [he] at hp
    omega

/-- The entire exact reset predecessor set of oddPre is forced onto its
    single even parent when 2*oddPre+5 has valuation at most two. -/
theorem no27_odd_parent_is_even (h n:Nat) (hn:13≤n)
    (hres : n%54=17 ∨ n%54=28 ∨ n%54=35 ∨ n%54=46)
    (hnot:(2*oddPre n+5)%27≠0)
    (hp:ResetParent h (oddPre n)) : h=gapHeight n := by
  have hband:=odd_even_band n hn hres
  have hg:=(gap_linear n hn hres).1
  have hpow:=pow_shift n (by omega)
  rcases hp with ⟨k,hb,heq⟩|⟨k,t,d,hd,hb,hout,heq⟩
  · have hk:k=n-2:=even_band_scale_unique (oddPre n) k (n-2) hb hband
    rw [hk] at heq
    omega
  · by_cases ht0:t=0
    · subst t
      have hnear:=odd_near_top n hn hres
      have hq : 2*oddPre n+5=3*d := by simpa using hout
      have hbad:=near_top_no_odd_tzero (oddPre n) (n-1) (by omega)
         hnear.1 hnear.2 ⟨k,d,by simpa using hb,hq⟩
      exact False.elim hbad
    · by_cases ht1:t=1
      · subst t
        have hq : 2*oddPre n+5=9*d := by simpa using hout
        have hl:=odd_linear n hn hres
        have hm:=exp_margin n hn
        have hs:=pow_shift_one n (by omega)
        have hlow:2^(n-1)<2*d:=by omega
        have hhigh:2*(2*d)+2<3*2^(n-1):=by omega
        exact False.elim ((gap_avoids_odd_images (n-1) (2*d) hlow hhigh)
           k (by simpa using hb))
      · have ht2:2≤t:=by omega
        have hex:t+1=3+(t-2):=by omega
        have hzero:3^(t+1)%27=0:=by
          rw [hex,Nat.pow_add]
          simp
        have hdiv:(2*oddPre n+5)%27=0:=by
          rw [hout,Nat.mul_mod,hzero]
          simp
        exact False.elim (hnot hdiv)

/-- The fourth odd-fork branch is unreachable from the genuine C(2,0) root
    in ALL four exact-two classes whenever the secondary valuation is <3. -/
theorem odd_fork_unreachable_no27 (n:Nat) (hn:13≤n)
    (hres : n%54=17 ∨ n%54=28 ∨ n%54=35 ∨ n%54=46)
    (hnot:(2*oddPre n+5)%27≠0) :
    ¬ReachC (2,0) (oddPre n,0) := by
  intro hr
  have hband := odd_even_band n hn hres
  have hne : oddPre n≠2 := by
    have hbig:=exp_margin n hn
    have hpow:=pow_shift n (by omega)
    omega
  have hchain:ResetChain 2 (oddPre n):=(root_reset_chain_iff (oddPre n)).mp hr
  obtain ⟨h,hpart,hparent⟩:=reset_chain_last hchain hne
  have heq:h=gapHeight n:=no27_odd_parent_is_even h n hn hres hnot hparent
  rw [heq] at hpart
  have hreach:ReachC (2,0) (gapHeight n,0):=(root_reset_chain_iff _).mpr hpart
  have hgap:=gap_bounds n hn hres
  exact (root_excludes_nonimage (gapHeight n) (gap_residue n hn hres)
    (gap_avoids_even_images n (gapHeight n) (by omega) hgap.1 hgap.2)) hreach

/-- For every fatal index in the four exact-two residue classes with a
    secondary no-27 gate, true-root halting reduces to the even parent. -/
theorem fatal_iff_even_under_no27 (n:Nat) (hn:13≤n)
    (hres : n%54=17 ∨ n%54=28 ∨ n%54=35 ∨ n%54=46)
    (hnot:(2*oddPre n+5)%27≠0) :
    ReachC (2,0) (fatal n,0) ↔ ReachC (2,0) (evenPre n,0) := by
  have hprior:=genuine_fatal_iff_two_parent_roots n (by omega) hres
  constructor
  · intro hr
    rcases hprior.mp hr with ho|he
    · exact False.elim ((odd_fork_unreachable_no27 n hn hres hnot) ho)
    · exact he
  · intro hr
    exact hprior.mpr (Or.inr hr)

#print axioms odd_fork_unreachable_no27
#print axioms fatal_iff_even_under_no27
end CascadeForkOddDead27
