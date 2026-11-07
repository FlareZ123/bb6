import TerminalCone
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Reachability can be transported back to the final exceptional
    dyadic level for arbitrary exponent k. Along the forced chain the
    weighted mass a+2*b falls by four at each genuine source edge. -/
theorem dyadic_back_iter (r t x b0 : Nat)
    (_hr : 8≤r) (htodd : t%2=1) (ht7 : 7≤t)
    (hbase : (x+2*b0)%4=3)
    (k a b : Nat) (hk : 1≤k) (hkr : k≤r)
    (hpow : b+2=2^k*t)
    (hmass : a+2*b+4*(r-k)=x+2*b0)
    (hre : BB6.Agent3.CReach a b) :
    ∃ A, BB6.Agent3.CReach A (2*t-2) ∧
      A+2*(2*t-2)+4*(r-1)=x+2*b0 := by
  induction k using Nat.strongRecOn generalizing a b with
  | ind k ih =>
      by_cases hk1 : k=1
      · subst k
        have hb : b=2*t-2 := by
          simp at hpow
          omega
        refine ⟨a, ?_, ?_⟩
        · simpa [hb] using hre
        · simpa only [hb] using hmass
      · have hk2 : 2≤k := by omega
        have hp : 4≤(2:Nat)^k := by
          have h := Nat.pow_le_pow_right (show 0<(2:Nat) by decide) hk2
          simpa using h
        have hmul : 4*t ≤ 2^k*t := Nat.mul_le_mul_right t hp
        have hb6 : 6≤b := by omega
        have hbe : b%2=0 := by
          have hp2: 2 ∣ (2:Nat)^k := by
            change 2^1 ∣ 2^k
            exact Nat.pow_dvd_pow 2 (by omega)
          obtain ⟨q,hq⟩ := hp2
          have hdiv : 2 ∣ b+2 := by
            refine ⟨q*t,?_⟩
            rw [hpow,hq]
            ac_rfl
          have hm : (b+2)%2=0 := Nat.mod_eq_zero_of_dvd hdiv
          omega
        have hbmod : b%8=2 ∨ b%8=6 := by
          by_cases h2 : k=2
          · subst k
            simp at hpow
            left
            omega
          · have h3 : 3≤k := by omega
            have hp8 : 8∣(2:Nat)^k := by
              change 2^3 ∣ 2^k
              exact Nat.pow_dvd_pow 2 (by omega)
            obtain ⟨q,hq⟩ := hp8
            have hdiv : 8 ∣ b+2 := by
              refine ⟨q*t,?_⟩
              rw [hpow,hq]
              ac_rfl
            have hm : (b+2)%8=0 := Nat.mod_eq_zero_of_dvd hdiv
            right
            omega
        have hm4 : (a+2*b+4*(r-k))%4=3 := by
          rw [hmass]
          exact hbase
        have hguard : (a+b)%8≠0 ∧ (a+b)%8≠7 := by
          rcases hbmod with hmod | hmod <;> omega
        have hnext := (six_even_right_blank_reach_iff
          a b hb6 hbe hguard.1 hguard.2).mp hre
        have hpowstep : 2^k*t=2*(2^(k-1)*t) := by
          have hpk : 2^k=2^(k-1)*2 := by
            calc
              2^k = 2^((k-1)+1) := by congr 1 <;> omega
              _ = 2^(k-1)*2 := Nat.pow_succ 2 (k-1)
          rw [hpk]
          ac_rfl
        have hnextPow : (b-2)/2+2=2^(k-1)*t := by
          rw [hpowstep] at hpow
          omega
        have hnextMass :
            (a+b-2)+2*((b-2)/2)+4*(r-(k-1))=x+2*b0 := by
          have hbh : 2*((b-2)/2)=b-2 := by omega
          rw [← hmass]
          omega
        exact ih (k-1) (by omega) (a+b-2) ((b-2)/2)
          (by omega) (by omega) hnextPow hnextMass hnext

/-- All-depth real-blank nonreachability of an alternative dyadic cone:
    r is any positive multiple of 8; x and t satisfy a joint residue
    condition. The final depth-r exception has two kinds of genuine
    parents, both certified impossible by TerminalCone. -/
theorem alternate_dyadic_no_blank (r x b0 t : Nat)
    (hr8 : 8≤r) (hr0 : r%8=0)
    (hx : x%16=3) (ht : t%8=7)
    (hpair : (x+30*t)%32=21)
    (hpow : b0+2=2^r*t) :
    ¬ BB6.Agent3.CReach x b0 := by
  have hp32 : 32 ∣ 2^r := by
    change 2^5 ∣ 2^r
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨u,hu⟩ := hp32
  have hdiv32 : 32 ∣ b0+2 := by
    refine ⟨u*t,?_⟩
    rw [hpow,hu]
    ac_rfl
  have hb032 : b0%32=30 := by
    have hm : (b0+2)%32=0 := Nat.mod_eq_zero_of_dvd hdiv32
    omega
  have hbase : (x+2*b0)%4=3 := by omega
  intro hre
  have hm0 : x+2*b0+4*(r-r)=x+2*b0 := by omega
  obtain ⟨A,hreach,hMass⟩ :=
    dyadic_back_iter r t x b0 hr8 (by omega) (by omega) hbase r x b0
      (by omega) (by omega) hpow hm0 hre
  have ht7 : 7≤t := by omega
  have hY : (2*t-2)%16=12 := by omega
  have hA : A%16=11 := by omega
  have hV : (A+(2*t-2)+1)%32=24 := by omega
  exact exceptional_no_blank A (2*t-2) hA hY hV hreach

/-- Every high stopping input in this mod-4096 parameter class is
    excluded at genuine blank origin. This is a uniformly quantified
    necessary restriction on Machine C's high stopping family. -/
theorem high_depth_eight_no_blank (j m k : Nat)
    (hm : 5≤m) (hj : j%16=0)
    (hparam : (j+3*m+3)%4096=2304)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  have hp4096 : 4096 ∣ 2^(2*m+2) := by
    change 2^12 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨u,hu⟩ := hp4096
  have hdiv4096 : 4096 ∣ 2^(2*m+2)*(j+3) := by
    refine ⟨u*(j+3),?_⟩
    rw [hu]
    ac_rfl
  have hstopmod : (k+j+3*m+5)%4096=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hdiv4096
  have hmod : (k+2)%4096=1792 := by omega
  let t := (k+2)/256
  have hpow : k+2=256*t := by
    dsimp [t]
    omega
  have ht : t%8=7 := by
    dsimp [t]
    omega
  have hxt : (2*j+3+30*t)%32=21 := by
    have ht16 : t%16=7 := by
      dsimp [t]
      omega
    omega
  have h8 : 2^8=256 := by decide
  have hpow8 : k+2=2^8*t := by rw [h8]; exact hpow
  exact alternate_dyadic_no_blank 8 (2*j+3) k t
    (by decide) (by decide) (by omega) ht hxt hpow8

#print axioms alternate_dyadic_no_blank
#print axioms high_depth_eight_no_blank
end BB6.Agent46
