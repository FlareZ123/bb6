import FourthBranch
set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace CascadeAgent10ExactlyTwo
open CascadeResetInverse CascadeUniformFatal CascadeAgent10Four CascadeAgent10FourthBranch

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

private theorem pow_mod_twentyseven (n : Nat) (hres : n%54=17 ∨ n%54=28 ∨ n%54=35 ∨ n%54=46) :
  (n%54=17 ∨ n%54=35) ∧ 2^n%27=2^17%27 ∨
  (n%54=28 ∨ n%54=46) ∧ 2^n%27=2^10%27 := by
  have hp := pow_mod_eighteen n
  rcases hres with h|h|h|h
  · left
    constructor
    · exact Or.inl h
    · have he:n%18=17:=by omega
      rw [hp,he]
  · right
    constructor
    · exact Or.inl h
    · have he:n%18=10:=by omega
      rw [hp,he]
  · left
    constructor
    · exact Or.inr h
    · have he:n%18=17:=by omega
      rw [hp,he]
  · right
    constructor
    · exact Or.inr h
    · have he:n%18=10:=by omega
      rw [hp,he]

/-- In four of the six n mod54 residue classes covered by the four-even ray,
    the fourth target has exactly two factors of three in 2u+5. -/
theorem fourth_not_div27 (n:Nat) (hn:10≤n)
    (hres:n%54=17 ∨ n%54=28 ∨ n%54=35 ∨ n%54=46) :
    (2*fourthPred n+5)%27 ≠ 0 := by
  have hbound : 31*n+49 ≤ 2^n := by
    have h : ∀ k:Nat,31*(k+10)+49 ≤ 2^(k+10) := by
      intro k
      induction k with
      | zero => decide
      | succ k ih =>
        rw [show k+1+10=k+10+1 by omega,Nat.pow_succ]
        omega
    have he:n=(n-10)+10:=by omega
    rw [he]
    exact h (n-10)
  have heq : 2*fourthPred n+5+62*n+93=8*2^n := by
    dsimp [fourthPred]
    omega
  have hp := pow_mod_twentyseven n hres
  rcases hp with ⟨hr,hm⟩|⟨hr,hm⟩
  · have hn27 : n%27=17 ∨ n%27=8 := by omega
    rcases hn27 with he|he
    · omega
    · omega
  · have hn27 : n%27=1 ∨ n%27=19 := by omega
    rcases hn27 with he|he
    · omega
    · omega

private theorem odd_band_scale_unique (v k j:Nat)
    (hb:6*2^k+1≤v ∧ v≤8*2^k-1)
    (hj:6*2^j+1≤v ∧ v≤8*2^j-1) : k=j := by
  by_cases heq:k=j
  · exact heq
  by_cases hlt:k<j
  · have hpow:2^(k+1)≤2^j:=Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega)
    have he:2^(k+1)=2*2^k := by rw [Nat.pow_succ];omega
    rw [he] at hpow
    omega
  · have hpow:2^(j+1)≤2^k:=Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega)
    have he:2^(j+1)=2*2^j := by rw [Nat.pow_succ];omega
    rw [he] at hpow
    omega

/-- Exact two-element complete reset-parent set for the four least
    3-adic exceptional mod54 classes, all n>=10 without a finite cutoff. -/
theorem fourth_parents_exactly_two (q n:Nat) (hn:10≤n)
    (hres:n%54=17 ∨ n%54=28 ∨ n%54=35 ∨ n%54=46) :
    ResetParent q (fourthPred n) ↔
      q = oddPre n ∨ q = evenPre n := by
  have hres18 : n%18=10 ∨ n%18=17 := by omega
  have hnon := fourth_not_div27 n hn hres
  have he := fourth_even_parent n hn
  have ho := fourth_odd_parent n hn hres18
  have hb : 3*2^n ≤ fourthPred n ∧ fourthPred n≤4*2^n ∧
      6*2^(n-1)-1 ≤ fourthPred n ∧ fourthPred n≤8*2^(n-1)-3 := by
    have hg : 31*n+49 ≤ 2^n := by
      have h : ∀ k:Nat,31*(k+10)+49 ≤ 2^(k+10) := by
        intro k
        induction k with
        | zero => decide
        | succ k ih =>
          rw [show k+1+10=k+10+1 by omega,Nat.pow_succ]
          omega
      have hh := h (n-10)
      have heq:n=(n-10)+10 := by omega
      rw [heq]
      exact hh
    have hp:2^n=2*2^(n-1):=by
      have hf:2^n=2^((n-1)+1):=congrArg (fun m:Nat=>2^m) (by omega)
      rw [Nat.pow_succ] at hf
      omega
    dsimp [fourthPred]
    rw [hp]
    omega
  constructor
  · intro hq
    rcases hq with ⟨k,hband,heq⟩|⟨k,t,d,hd,hband,hout,heq⟩
    · have hk:k=n-1:=even_band_scale_unique (fourthPred n) k (n-1) hband ⟨hb.2.2.1,hb.2.2.2⟩
      have heq2 : 2*fourthPred n = 8*2^(n-1)+evenPre n+(n-1) := by
        have hg:=fifth_growth n hn
        have hp:2^n=2*2^(n-1):=by
          have hf:2^n=2^((n-1)+1):=congrArg (fun m:Nat=>2^m) (by omega)
          rw [Nat.pow_succ] at hf
          omega
        dsimp [evenPre,fourthPred]
        rw [hp]
        omega
      right
      rw [hk] at heq
      omega
    · by_cases ht:t=0
      · subst t
        have ht0 : 2*fourthPred n+5=3*d := by simpa using hout
        exact False.elim (near_top_no_odd_tzero (fourthPred n) n (by omega) hb.1 hb.2.1 ⟨k,d,by simpa using hband,ht0⟩)
      · have ht1:1≤t:=by omega
        have h2:t=1:=by
          by_cases h2:t=1
          · exact h2
          have hge:2≤t:=by omega
          have hex:t+1=3+(t-2):=by omega
          have hpow:3^(t+1)%27=0:=by
            rw [hex,Nat.pow_add]
            simp
          have hzero:(2*fourthPred n+5)%27=0:=by
            rw [hout,Nat.mul_mod,hpow]
            simp
          exact False.elim (hnon hzero)
        subst t
        have hf := odd_factor n hn hres18
        have hd_eq : d = CascadeAgent10FourthBranch.d n := by
          have hh : 2*fourthPred n+5=9*d := by simpa using hout
          omega
        have hob := odd_band n hn hres18
        have heq2 : 2*(2*CascadeAgent10FourthBranch.d n) =
            8*2^(n-2)+oddPre n+(n-2)+5 := by
          have hg:=fifth_growth n hn
          have hp:2^n=4*2^(n-2):=by
            have hh:2^n=2^((n-2)+2):=congrArg (fun m:Nat=>2^m) (by omega)
            rw [Nat.pow_add] at hh
            omega
          dsimp [oddPre]
          omega
        have hk:k=n-2 := odd_band_scale_unique (2*CascadeAgent10FourthBranch.d n)
          k (n-2) (by simpa [hd_eq] using hband) hob
        left
        rw [hd_eq,hk] at heq
        omega
  · rintro (rfl|rfl)
    · exact ho
    · exact he

/-- Four forced source-reset levels followed by the *complete* genuine-root
    two-branch disjunction in four unbounded mod54 index classes. -/
theorem genuine_fatal_iff_two_parent_roots (n:Nat) (hn:10≤n)
    (hres:n%54=17 ∨ n%54=28 ∨ n%54=35 ∨ n%54=46) :
    CascadeSweep.ReachC (2,0) (CascadeManyShield.fatal n,0) ↔
      CascadeSweep.ReachC (2,0) (oddPre n,0) ∨
      CascadeSweep.ReachC (2,0) (evenPre n,0) := by
  have h18 : n%18=10 ∨ n%18=17 := by omega
  have hcore := genuine_fatal_iff_fourth n hn h18
  rw [hcore]
  have hne:fourthPred n ≠2 := by
    have hb:=fifth_growth n hn
    dsimp [fourthPred]
    omega
  constructor
  · intro hr
    have hc : ResetChain 2 (fourthPred n) :=
      (root_reset_chain_iff (fourthPred n)).mp hr
    obtain ⟨p,hchain,hparent⟩ := reset_chain_last hc hne
    have hp := (fourth_parents_exactly_two p n hn hres).mp hparent
    rcases hp with hp|hp
    · left
      rw [hp] at hchain
      exact (root_reset_chain_iff (oddPre n)).mpr hchain
    · right
      rw [hp] at hchain
      exact (root_reset_chain_iff (evenPre n)).mpr hchain
  · intro hr
    rcases hr with hr|hr
    · have hc := (root_reset_chain_iff (oddPre n)).mp hr
      exact (root_reset_chain_iff (fourthPred n)).mpr
        (hc.append (fourth_odd_parent n hn h18))
    · have hc := (root_reset_chain_iff (evenPre n)).mp hr
      exact (root_reset_chain_iff (fourthPred n)).mpr
        (hc.append (fourth_even_parent n hn))

#print axioms fourth_not_div27
#print axioms fourth_parents_exactly_two
#print axioms genuine_fatal_iff_two_parent_roots
end CascadeAgent10ExactlyTwo
