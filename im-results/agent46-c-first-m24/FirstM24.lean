import OddOddLowVal
import ReachAffine
import Agent3CImage
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
namespace BB6.Agent46

private theorem first_power_linear (m : Nat) :
    8*(m+1) ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have hh : 2^(2*(m+1)+3) = 4*2^(2*m+3) := by
      have he : 2*(m+1)+3=(2*m+3)+2 := by omega
      rw [he, Nat.pow_add]
      simp [Nat.mul_comm]
    rw [hh]
    omega

/-- An entire infinite first-stopping family on the genuine Machine C blank
    section is excluded by the exactly forced affine and odd/odd predecessors. -/
theorem first_halt_m24_mod32_unreachable (m k time : Nat)
    (hm : m%32=24)
    (hgate : k+3*m+4=2^(2*m+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (1,k) := by
  have hm24 : 24≤m := by omega
  let P : Nat := 2^(2*m+3)
  have hpdiv : 128 ∣ P := by
    dsimp [P]
    change 2^7 ∣ 2^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨r,hr⟩ := hpdiv
  have hmod : (k+3*m+4)%128=0 := by
    have hd : 128 ∣ k+3*m+4 := by
      refine ⟨r, ?_⟩
      change k+3*m+4=P at hgate
      rw [hgate,hr]
    exact Nat.mod_eq_zero_of_dvd hd
  have hpow : 8*(m+1) ≤ P := by
    exact first_power_linear m
  have hkbig : 100≤k := by
    change k+3*m+4=P at hgate
    omega
  let a := k-1
  let b := (k-2)/2
  let c := (a+b-4)/2
  let d := (a+3*b-10)/4
  have hall :
     k%2=0 ∧ (1+k)%4=1 ∧
     a%2=1 ∧ b%2=1 ∧ (a+b)%4=0 ∧ (a+b)%16≠0 ∧
     d%2=1 ∧ (c+d)%4=1 := by
    dsimp [a,b,c,d]
    omega
  rcases hall with ⟨hke,hk4,haodd,hbodd,hab4,hab16,hdodd,hcd4⟩
  have hb5 : 5≤b := by dsimp [b]; omega
  have hab24 : 24≤a+b := by dsimp [a,b]; omega
  have hd5 : 5≤d := by dsimp [d,a,b]; omega
  intro h
  obtain ⟨n1,hn1⟩ :=
    (BB6.Agent15.blank_reach_iff_affine 1 k (by omega) hke hk4).mp
      ⟨time,h⟩
  have haa : 1+k-2=a := by dsimp [a]; omega
  rw [haa] at hn1
  change BB6.Agent8Section.run secNext n1 (some (5,1)) = some (a,b) at hn1
  have hreach2 : ∃ n, BB6.Agent8Section.run secNext n (some (5,1)) = some (c,d) :=
    (BB6.Agent3.oddodd_lowval_blank_reach_iff a b haodd hbodd hb5 hab4 hab16 hab24).mp
      ⟨n1,by simpa [c,d] using hn1⟩
  obtain ⟨n2,hn2⟩ := hreach2
  cases n2 with
  | zero =>
      have hs : (c,d)=(5,1) := by
        simpa [BB6.Agent8Section.run] using hn2.symm
      have h : d=1 := congrArg Prod.snd hs
      omega
  | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n c d hn2 hd5 hdodd
      omega

#print axioms first_halt_m24_mod32_unreachable
end BB6.Agent46
