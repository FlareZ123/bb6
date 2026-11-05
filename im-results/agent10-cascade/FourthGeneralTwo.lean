import FourthNoDiv81
set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace CascadeAgent10GeneralTwo
open CascadeResetInverse CascadeUniformFatal CascadeAgent10Four CascadeAgent10FourthBranch CascadeAgent10ExactlyTwo CascadeAgent10OddGap CascadeAgent10Mod81

theorem fourth_parents_two_of_non81 (q n:Nat) (hn:10≤n)
    (hres18:n%18=10 ∨ n%18=17) (hnon81:(2*fourthPred n+5)%81≠0) :
    ResetParent q (fourthPred n) ↔
      q = oddPre n ∨ q = evenPre n := by
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
          by_cases hh:t=1
          · exact hh
          by_cases htwo:t=2
          · subst t
            have hq:2*fourthPred n+5=27*d := by simpa using hout
            exact False.elim (fourth_no_odd_ttwo n hn ⟨k,d,by simpa using hband,hq⟩)
          have hge:3≤t:=by omega
          have hex:t+1=4+(t-3):=by omega
          have hpow:3^(t+1)%81=0:=by
            rw [hex,Nat.pow_add]
            simp
          have hzero:(2*fourthPred n+5)%81=0:=by
            rw [hout,Nat.mul_mod,hpow]
            simp
          exact False.elim (hnon81 hzero)
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

theorem genuine_fatal_iff_two_under_non81 (n:Nat) (hn:10≤n)
    (h18:n%18=10 ∨ n%18=17) (hnon81:(2*fourthPred n+5)%81≠0) :
    CascadeSweep.ReachC (2,0) (CascadeManyShield.fatal n,0) ↔
      CascadeSweep.ReachC (2,0) (oddPre n,0) ∨
      CascadeSweep.ReachC (2,0) (evenPre n,0) := by
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
    have hp := (fourth_parents_two_of_non81 p n hn h18 hnon81).mp hparent
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

/-- All but two of the 18 n mod162 sectors satisfying the real fatal
    index condition have an EXACT two-parent blank-root gate. -/
theorem genuine_fatal_iff_two_on_16_of_18 (n:Nat) (hn:10≤n)
    (h18:n%18=10 ∨ n%18=17)
    (h64:n%162≠64) (h107:n%162≠107) :
    CascadeSweep.ReachC (2,0) (CascadeManyShield.fatal n,0) ↔
      CascadeSweep.ReachC (2,0) (oddPre n,0) ∨
      CascadeSweep.ReachC (2,0) (evenPre n,0) := by
  by_cases hgood:n%54=17 ∨ n%54=28 ∨ n%54=35 ∨ n%54=46
  · exact genuine_fatal_iff_two_parent_roots n hn hgood
  · have hrem:n%162=10 ∨ n%162=53 ∨ n%162=118 ∨ n%162=161 := by omega
    have hnodiv:=fourth_not_div81 n hn hrem
    exact genuine_fatal_iff_two_under_non81 n hn h18 hnodiv

#print axioms fourth_parents_two_of_non81
#print axioms genuine_fatal_iff_two_on_16_of_18
end CascadeAgent10GeneralTwo
