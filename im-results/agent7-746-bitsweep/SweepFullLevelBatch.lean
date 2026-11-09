import SweepAdjacentFatal
import SweepEvenOrbit

namespace CascadeFastReturn
open CascadeBitSweep

/-- A successful nonfatal first reset whose deficit is exactly twice an
    admissible residual stays at the same level and halves that deficit. -/
theorem full_level_half_step (k h d : Nat)
    (hk : firstFailIndex h=k)
    (hnot : ¬fatalAt h)
    (hd : deficitAt k h=2*d)
    (hmin : 2*k+6≤d) :
    ∃u, bitOutcome h=some u ∧ firstFailIndex u=k ∧ deficitAt k u=d := by
  let p := 2^k
  let u := 4*p+(h+k)/2
  have hh := (firstFailIndex_spec h).2
  rw [hk] at hh
  have hbound : h≤8*p+k := by omega
  have hrepr : 8*p+k-h=2*d := hd
  have hpar : (h+k)%2=0 := by omega
  have hfat : h+k+4≠4*p := by
    intro he
    apply hnot
    dsimp [fatalAt]
    rw [hk]
    exact he
  have he : bitOutcome h=some u := by
    simp [bitOutcome,hk,hfat,hpar,u,p]
  have hdlarge : 4*k+12≤deficitAt k h := by omega
  have hu : firstFailIndex u=k := by
    have hp := (even_edge_same_iff_large_deficit h u he (by rw [hk]; exact hpar)).2
    have hresult := hp (by rw [hk]; exact hdlarge)
    rwa [hk] at hresult
  have htwice := bitOutcome_even_deficit_halves h k u hk hpar he
  have hdu : deficitAt k u=d := by omega
  exact ⟨u,he,hu,hdu⟩

/-- Exact all-source same-level batch, including original heights below the
    synthetic 4·2^k cutoff. -/
theorem runBit_full_level_block (k h m d : Nat)
    (hk : firstFailIndex h=k)
    (hnot : ¬fatalAt h)
    (hmin : 2*k+6≤d)
    (hfactor : deficitAt k h=2^m*d) :
    ∃u, runBit h m=some u ∧ firstFailIndex u=k ∧
      deficitAt k u=d ∧ ¬fatalAt u := by
  induction m generalizing h with
  | zero =>
    refine ⟨h,rfl,hk,?_,hnot⟩
    simpa using hfactor
  | succ m ih =>
    have hpow : 2^(m+1)*d=2*(2^m*d) := by rw [Nat.pow_succ]; ac_rfl
    have hd : deficitAt k h=2*(2^m*d) := by rw [hfactor,hpow]
    have hpowmin : 2*k+6≤2^m*d := by
      have pp : 1≤2^m := Nat.one_le_pow m 2 (by decide)
      have pq := Nat.mul_le_mul_right d pp
      omega
    obtain ⟨u,he,hu,hdu⟩ := full_level_half_step k h (2^m*d) hk hnot hd hpowmin
    have hnotu : ¬fatalAt u := same_level_edge_not_fatal h u he (hk.trans hu.symm)
    obtain ⟨v,hv,hkv,hdv,hnv⟩ := ih u hu hnotu hdu
    refine ⟨v,?_,hkv,hdv,hnv⟩
    rw [runBit_succ_start,he]
    simpa using hv

/-- Every admissible upper-band deficit can be factored by halving until
    its terminal residual is odd or below the next-even-step cutoff. -/
theorem level_terminal_factor (k D : Nat)
    (hmin : 2*k+6≤D) :
    ∃m d, D=2^m*d ∧ 2*k+6≤d ∧ (d%2=1 ∨ d<4*k+12) := by
  induction D using Nat.strongRecOn with
  | ind D ih =>
    by_cases hdodd : D%2=1
    · exact ⟨0,D,by simp,hmin,Or.inl hdodd⟩
    by_cases hdsmall : D<4*k+12
    · exact ⟨0,D,by simp,hmin,Or.inr hdsmall⟩
    have hdeven : D%2=0 := by omega
    have hhalf : D=2*(D/2) := by omega
    have hhalfmin : 2*k+6≤D/2 := by omega
    have hhalfbelow : D/2<D := by omega
    obtain ⟨m,d,he,hdmin,hexit⟩ := ih (D/2) hhalfbelow hhalfmin
    refine ⟨m+1,d,?_,hdmin,hexit⟩
    calc
      D = 2*(D/2) := hhalf
      _ = 2*(2^m*d) := by rw [he]
      _ = 2^(m+1)*d := by rw [Nat.pow_succ]; ac_rfl

/-- The original first-failed-level guard gives an exact deficit floor. -/
theorem level_deficit_min (h : Nat) :
    2*firstFailIndex h+6 ≤ deficitAt (firstFailIndex h) h := by
  have hh := (firstFailIndex_spec h).2
  dsimp [deficitAt]
  omega

/-- The source branch parity agrees with the same-level deficit parity. -/
theorem deficit_parity (k h : Nat) (hk : firstFailIndex h=k) :
    (h+k)%2=(deficitAt k h)%2 := by
  have hh := (firstFailIndex_spec h).2
  rw [hk] at hh
  have hbound : h≤8*2^k+k := by omega
  dsimp [deficitAt]
  omega

/-- An odd or short terminal deficit entails halt or an actual level exit. -/
theorem full_level_terminal_next (k u d : Nat)
    (hk : firstFailIndex u=k)
    (hdef : deficitAt k u=d)
    (hexit : d%2=1 ∨ d<4*k+12) :
    bitOutcome u=none ∨ ∃v, bitOutcome u=some v ∧ k<firstFailIndex v := by
  cases he : bitOutcome u with
  | none => exact Or.inl rfl
  | some v =>
    right
    refine ⟨v,rfl,?_⟩
    have hpar : (u+k)%2=d%2 := by
      rw [deficit_parity k u hk, hdef]
    rcases hexit with hod | hsmall
    · exact (by simpa [hk] using bitOutcome_odd_address_increases u v he (by rw [hk]; omega))
    · by_cases heven : (u+k)%2=0
      · have hcap := (even_edge_advance_iff_small_deficit u v he (by rw [hk]; exact heven)).2
          (by rw [hk,hdef]; exact hsmall)
        rw [hk] at hcap
        omega
      · have hodd : (u+k)%2=1 := by omega
        have hcross := bitOutcome_odd_address_increases u v he (by rw [hk]; exact hodd)
        rw [hk] at hcross
        exact hcross

/-- Every nonfatal source-C reset height has a finite source-exact
    same-level block, then one terminal reset which halts or raises the
    level. This covers authentic blank-root heights without assumptions
    about synthetic preparation, and leaves the unbounded level sequence open. -/
theorem source_level_normal_form (h : Nat) (hnot : ¬fatalAt h) :
    ∃m u, runBit h m=some u ∧
      firstFailIndex u=firstFailIndex h ∧
      (bitOutcome u=none ∨ ∃v, bitOutcome u=some v ∧
         firstFailIndex u<firstFailIndex v) := by
  let k := firstFailIndex h
  let D := deficitAt k h
  have hmin : 2*k+6≤D := level_deficit_min h
  obtain ⟨m,d,hfactor,hdmin,hexit⟩ := level_terminal_factor k D hmin
  obtain ⟨u,hrun,hu,hdu,hnotu⟩ :=
    runBit_full_level_block k h m d rfl hnot hdmin hfactor
  refine ⟨m,u,hrun,hu,?_⟩
  simpa only [hu] using full_level_terminal_next k u d hu hdu hexit

#print axioms full_level_half_step
#print axioms runBit_full_level_block
#print axioms level_terminal_factor
#print axioms source_level_normal_form
end CascadeFastReturn
