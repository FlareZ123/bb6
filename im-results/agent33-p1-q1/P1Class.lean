import P1InverseFixed
import ConeKernel
import P1TwoSector
import Std
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
namespace BB6.Agent33Q1Class
open BB6.Agent4Cone
open BB6.Agent47P1
open BB6.Agent45TwoRoot
open BB6.P1Reduction

private theorem no_power_in_band (n x : Nat)
    (hl : 28*2^n < x+12) (hu : x+12 < 56*2^n) :
    ∀ j : Nat, x+12 ≠ 14*2^j := by
  intro j he
  by_cases hj : j≤n+1
  · have hp := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hj
    have hpow : 2^(n+1)=2*2^n := by rw [Nat.pow_succ]; omega
    omega
  · have hp := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (show n+2≤j by omega)
    have hpow : 2^(n+2)=4*2^n := by rw [Nat.pow_add]; omega
    omega

private theorem no_power_class (S w x : Nat)
    (hP : 2^(16*(2048*w+1))=65536*S)
    (hl : 28*65536*S<x+12) (hu : x+12<56*65536*S) :
    ∀ j : Nat, x+12 ≠ 14*2^j := by
  have hlp : 28*2^(16*(2048*w+1))<x+12 := by rw [hP]; simpa only [← Nat.mul_assoc] using hl
  have hup : x+12<56*2^(16*(2048*w+1)) := by rw [hP]; simpa only [← Nat.mul_assoc] using hu
  exact no_power_in_band _ x hlp hup

private theorem block_L0_1_1_0_1_0_0_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (267008*S-4768*w-16) (3403008*S-60768*w-55) := by
  have h0 : inverseAt (267008*S-4768*w-16) (3403008*S-60768*w-55) 0 = some ((66752*S-1192*w-5),(3536512*S-63152*w-63)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (267008*S-4768*w-16) (3403008*S-60768*w-55) 1 = some ((950880*S-16980*w-21),(1768256*S-31576*w-33)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (3536512*S-63152*w-63) ∧ (3536512*S-63152*w-63)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (267008*S-4768*w-16) (3403008*S-60768*w-55) 2 = some ((1392944*S-24874*w-29),(884128*S-15788*w-18)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1768256*S-31576*w-33) ∧ (1768256*S-31576*w-33)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((3403008*S-60768*w-55)+(267008*S-4768*w-16)/2+3)%2^(2+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (267008*S-4768*w-16) (3403008*S-60768*w-55) k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((66752*S-1192*w-5),(3536512*S-63152*w-63)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((950880*S-16980*w-21),(1768256*S-31576*w-33)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1392944*S-24874*w-29),(884128*S-15788*w-18)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (267008*S-4768*w-16) (3403008*S-60768*w-55) k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((66752*S-1192*w-5),(3536512*S-63152*w-63)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (133504*S-2384*w-14) := by omega
      have hy : c+4 = (3536512*S-63152*w-59) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((950880*S-16980*w-21),(1768256*S-31576*w-33)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1901760*S-33960*w-46) := by omega
      have hy : c+4 = (1768256*S-31576*w-29) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1392944*S-24874*w-29),(884128*S-15788*w-18)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2785888*S-49748*w-62) := by omega
      have hy : c+4 = (884128*S-15788*w-14) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_1_1_0_1_0_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (534016*S-9536*w-20) (3136000*S-56000*w-49) := by
  have h0 : inverseAt (534016*S-9536*w-20) (3136000*S-56000*w-49) 0 = some ((133504*S-2384*w-6),(3403008*S-60768*w-59)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (534016*S-9536*w-20) (3136000*S-56000*w-49) 1 = some ((984256*S-17576*w-21),(1701504*S-30384*w-31)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (3403008*S-60768*w-59) ∧ (3403008*S-60768*w-59)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (534016*S-9536*w-20) (3136000*S-56000*w-49) 2 = some ((1409632*S-25172*w-29),(850752*S-15192*w-17)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1701504*S-30384*w-31) ∧ (1701504*S-30384*w-31)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h3 : inverseAt (534016*S-9536*w-20) (3136000*S-56000*w-49) 3 = some ((1622320*S-28970*w-33),(425376*S-7596*w-10)) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ (850752*S-15192*w-17) ∧ (850752*S-15192*w-17)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((3136000*S-56000*w-49)+(534016*S-9536*w-20)/2+3)%2^(3+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (534016*S-9536*w-20) (3136000*S-56000*w-49) k 1 3 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((133504*S-2384*w-6),(3403008*S-60768*w-59)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((984256*S-17576*w-21),(1701504*S-30384*w-31)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1409632*S-25172*w-29),(850752*S-15192*w-17)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=((1622320*S-28970*w-33),(425376*S-7596*w-10)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (534016*S-9536*w-20) (3136000*S-56000*w-49) k c 3 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((133504*S-2384*w-6),(3403008*S-60768*w-59)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (267008*S-4768*w-16) := by omega
      have hy : c+4 = (3403008*S-60768*w-55) := by omega
      rw [hx,hy]
      exact block_L0_1_1_0_1_0_0_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((984256*S-17576*w-21),(1701504*S-30384*w-31)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1968512*S-35152*w-46) := by omega
      have hy : c+4 = (1701504*S-30384*w-27) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1409632*S-25172*w-29),(850752*S-15192*w-17)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2819264*S-50344*w-62) := by omega
      have hy : c+4 = (850752*S-15192*w-13) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h3] at hval
      have hp : (k,c)=((1622320*S-28970*w-33),(425376*S-7596*w-10)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3244640*S-57940*w-70) := by omega
      have hy : c+4 = (425376*S-7596*w-6) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_1_1_0_0_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (301056*S-5376*w-16) (3368960*S-60160*w-49) := by
  have h0 : inverseAt (301056*S-5376*w-16) (3368960*S-60160*w-49) 0 = some ((75264*S-1344*w-5),(3519488*S-62848*w-57)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (301056*S-5376*w-16) (3368960*S-60160*w-49) 1 = some ((955136*S-17056*w-19),(1759744*S-31424*w-30)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (3519488*S-62848*w-57) ∧ (3519488*S-62848*w-57)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((3368960*S-60160*w-49)+(301056*S-5376*w-16)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (301056*S-5376*w-16) (3368960*S-60160*w-49) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((75264*S-1344*w-5),(3519488*S-62848*w-57)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((955136*S-17056*w-19),(1759744*S-31424*w-30)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (301056*S-5376*w-16) (3368960*S-60160*w-49) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((75264*S-1344*w-5),(3519488*S-62848*w-57)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (150528*S-2688*w-14) := by omega
      have hy : c+4 = (3519488*S-62848*w-53) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((955136*S-17056*w-19),(1759744*S-31424*w-30)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1910272*S-34112*w-42) := by omega
      have hy : c+4 = (1759744*S-31424*w-26) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_1_1_0_1_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (1068032*S-19072*w-28) (2601984*S-46464*w-39) := by
  have h0 : inverseAt (1068032*S-19072*w-28) (2601984*S-46464*w-39) 0 = some ((267008*S-4768*w-8),(3136000*S-56000*w-53)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (1068032*S-19072*w-28) (2601984*S-46464*w-39) 1 = some ((1051008*S-18768*w-21),(1568000*S-28000*w-28)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (3136000*S-56000*w-53) ∧ (3136000*S-56000*w-53)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((2601984*S-46464*w-39)+(1068032*S-19072*w-28)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1068032*S-19072*w-28) (2601984*S-46464*w-39) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((267008*S-4768*w-8),(3136000*S-56000*w-53)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1051008*S-18768*w-21),(1568000*S-28000*w-28)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1068032*S-19072*w-28) (2601984*S-46464*w-39) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((267008*S-4768*w-8),(3136000*S-56000*w-53)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (534016*S-9536*w-20) := by omega
      have hy : c+4 = (3136000*S-56000*w-49) := by omega
      rw [hx,hy]
      exact block_L0_1_1_0_1_0_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1051008*S-18768*w-21),(1568000*S-28000*w-28)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2102016*S-37536*w-46) := by omega
      have hy : c+4 = (1568000*S-28000*w-24) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_1_1_0_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (602112*S-10752*w-20) (3067904*S-54784*w-43) := by
  have h0 : inverseAt (602112*S-10752*w-20) (3067904*S-54784*w-43) 0 = some ((150528*S-2688*w-6),(3368960*S-60160*w-53)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (602112*S-10752*w-20) (3067904*S-54784*w-43) 1 = some ((992768*S-17728*w-19),(1684480*S-30080*w-28)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (3368960*S-60160*w-53) ∧ (3368960*S-60160*w-53)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((3067904*S-54784*w-43)+(602112*S-10752*w-20)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (602112*S-10752*w-20) (3067904*S-54784*w-43) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((150528*S-2688*w-6),(3368960*S-60160*w-53)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((992768*S-17728*w-19),(1684480*S-30080*w-28)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (602112*S-10752*w-20) (3067904*S-54784*w-43) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((150528*S-2688*w-6),(3368960*S-60160*w-53)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (301056*S-5376*w-16) := by omega
      have hy : c+4 = (3368960*S-60160*w-49) := by omega
      rw [hx,hy]
      exact block_L0_1_1_0_0_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((992768*S-17728*w-19),(1684480*S-30080*w-28)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1985536*S-35456*w-42) := by omega
      have hy : c+4 = (1684480*S-30080*w-24) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_1_1_0_1_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (2136064*S-38144*w-44) (1533952*S-27392*w-21) := by
  have h0 : inverseAt (2136064*S-38144*w-44) (1533952*S-27392*w-21) 0 = some ((534016*S-9536*w-12),(2601984*S-46464*w-43)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (2136064*S-38144*w-44) (1533952*S-27392*w-21) 1 = some ((1184512*S-21152*w-23),(1300992*S-23232*w-23)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2601984*S-46464*w-43) ∧ (2601984*S-46464*w-43)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (2136064*S-38144*w-44) (1533952*S-27392*w-21) 2 = some ((1509760*S-26960*w-29),(650496*S-11616*w-13)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1300992*S-23232*w-23) ∧ (1300992*S-23232*w-23)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h3 : inverseAt (2136064*S-38144*w-44) (1533952*S-27392*w-21) 3 = some ((1672384*S-29864*w-32),(325248*S-5808*w-8)) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ (650496*S-11616*w-13) ∧ (650496*S-11616*w-13)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((1533952*S-27392*w-21)+(2136064*S-38144*w-44)/2+3)%2^(3+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2136064*S-38144*w-44) (1533952*S-27392*w-21) k 1 3 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((534016*S-9536*w-12),(2601984*S-46464*w-43)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1184512*S-21152*w-23),(1300992*S-23232*w-23)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1509760*S-26960*w-29),(650496*S-11616*w-13)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=((1672384*S-29864*w-32),(325248*S-5808*w-8)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2136064*S-38144*w-44) (1533952*S-27392*w-21) k c 3 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((534016*S-9536*w-12),(2601984*S-46464*w-43)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1068032*S-19072*w-28) := by omega
      have hy : c+4 = (2601984*S-46464*w-39) := by omega
      rw [hx,hy]
      exact block_L0_1_1_0_1_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1184512*S-21152*w-23),(1300992*S-23232*w-23)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2369024*S-42304*w-50) := by omega
      have hy : c+4 = (1300992*S-23232*w-19) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1509760*S-26960*w-29),(650496*S-11616*w-13)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3019520*S-53920*w-62) := by omega
      have hy : c+4 = (650496*S-11616*w-9) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h3] at hval
      have hp : (k,c)=((1672384*S-29864*w-32),(325248*S-5808*w-8)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3344768*S-59728*w-68) := by omega
      have hy : c+4 = (325248*S-5808*w-4) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (3344768*S-59728*w-68) hP (by omega) (by omega)

private theorem block_L0_1_3_0_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (838656*S-14976*w-24) (2831360*S-50560*w-43) := by
  have h0 : inverseAt (838656*S-14976*w-24) (2831360*S-50560*w-43) 0 = some ((209664*S-3744*w-7),(3250688*S-58048*w-55)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (838656*S-14976*w-24) (2831360*S-50560*w-43) 1 = some ((1022336*S-18256*w-21),(1625344*S-29024*w-29)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (3250688*S-58048*w-55) ∧ (3250688*S-58048*w-55)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (838656*S-14976*w-24) (2831360*S-50560*w-43) 2 = some ((1428672*S-25512*w-28),(812672*S-14512*w-16)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1625344*S-29024*w-29) ∧ (1625344*S-29024*w-29)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((2831360*S-50560*w-43)+(838656*S-14976*w-24)/2+3)%2^(2+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (838656*S-14976*w-24) (2831360*S-50560*w-43) k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((209664*S-3744*w-7),(3250688*S-58048*w-55)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1022336*S-18256*w-21),(1625344*S-29024*w-29)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1428672*S-25512*w-28),(812672*S-14512*w-16)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (838656*S-14976*w-24) (2831360*S-50560*w-43) k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((209664*S-3744*w-7),(3250688*S-58048*w-55)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (419328*S-7488*w-18) := by omega
      have hy : c+4 = (3250688*S-58048*w-51) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1022336*S-18256*w-21),(1625344*S-29024*w-29)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2044672*S-36512*w-46) := by omega
      have hy : c+4 = (1625344*S-29024*w-25) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1428672*S-25512*w-28),(812672*S-14512*w-16)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2857344*S-51024*w-60) := by omega
      have hy : c+4 = (812672*S-14512*w-12) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (2857344*S-51024*w-60) hP (by omega) (by omega)

private theorem block_L0_1_3_0_1_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (2254336*S-40256*w-48) (1415680*S-25280*w-21) := by
  have h0 : inverseAt (2254336*S-40256*w-48) (1415680*S-25280*w-21) 0 = some ((563584*S-10064*w-13),(2542848*S-45408*w-45)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (2254336*S-40256*w-48) (1415680*S-25280*w-21) 1 = some ((1199296*S-21416*w-24),(1271424*S-22704*w-24)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2542848*S-45408*w-45) ∧ (2542848*S-45408*w-45)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((1415680*S-25280*w-21)+(2254336*S-40256*w-48)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2254336*S-40256*w-48) (1415680*S-25280*w-21) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((563584*S-10064*w-13),(2542848*S-45408*w-45)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1199296*S-21416*w-24),(1271424*S-22704*w-24)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2254336*S-40256*w-48) (1415680*S-25280*w-21) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((563584*S-10064*w-13),(2542848*S-45408*w-45)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1127168*S-20128*w-30) := by omega
      have hy : c+4 = (2542848*S-45408*w-41) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1199296*S-21416*w-24),(1271424*S-22704*w-24)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2398592*S-42832*w-52) := by omega
      have hy : c+4 = (1271424*S-22704*w-20) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (2398592*S-42832*w-52) hP (by omega) (by omega)

private theorem block_L0_4_1_0_1_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (2173696*S-38816*w-48) (1496320*S-26720*w-23) := by
  have h0 : inverseAt (2173696*S-38816*w-48) (1496320*S-26720*w-23) 0 = some ((543424*S-9704*w-13),(2583168*S-46128*w-47)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (2173696*S-38816*w-48) (1496320*S-26720*w-23) 1 = some ((1189216*S-21236*w-25),(1291584*S-23064*w-25)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2583168*S-46128*w-47) ∧ (2583168*S-46128*w-47)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (2173696*S-38816*w-48) (1496320*S-26720*w-23) 2 = some ((1512112*S-27002*w-31),(645792*S-11532*w-14)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1291584*S-23064*w-25) ∧ (1291584*S-23064*w-25)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((1496320*S-26720*w-23)+(2173696*S-38816*w-48)/2+3)%2^(2+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2173696*S-38816*w-48) (1496320*S-26720*w-23) k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((543424*S-9704*w-13),(2583168*S-46128*w-47)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1189216*S-21236*w-25),(1291584*S-23064*w-25)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1512112*S-27002*w-31),(645792*S-11532*w-14)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2173696*S-38816*w-48) (1496320*S-26720*w-23) k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((543424*S-9704*w-13),(2583168*S-46128*w-47)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1086848*S-19408*w-30) := by omega
      have hy : c+4 = (2583168*S-46128*w-43) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1189216*S-21236*w-25),(1291584*S-23064*w-25)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2378432*S-42472*w-54) := by omega
      have hy : c+4 = (1291584*S-23064*w-21) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1512112*S-27002*w-31),(645792*S-11532*w-14)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3024224*S-54004*w-66) := by omega
      have hy : c+4 = (645792*S-11532*w-10) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_4_1_1_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (1256192*S-22432*w-32) (2413824*S-43104*w-39) := by
  have h0 : inverseAt (1256192*S-22432*w-32) (2413824*S-43104*w-39) 0 = some ((314048*S-5608*w-9),(3041920*S-54320*w-55)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (1256192*S-22432*w-32) (2413824*S-43104*w-39) 1 = some ((1074528*S-19188*w-23),(1520960*S-27160*w-29)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (3041920*S-54320*w-55) ∧ (3041920*S-54320*w-55)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (1256192*S-22432*w-32) (2413824*S-43104*w-39) 2 = some ((1454768*S-25978*w-30),(760480*S-13580*w-16)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1520960*S-27160*w-29) ∧ (1520960*S-27160*w-29)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((2413824*S-43104*w-39)+(1256192*S-22432*w-32)/2+3)%2^(2+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1256192*S-22432*w-32) (2413824*S-43104*w-39) k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((314048*S-5608*w-9),(3041920*S-54320*w-55)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1074528*S-19188*w-23),(1520960*S-27160*w-29)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1454768*S-25978*w-30),(760480*S-13580*w-16)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1256192*S-22432*w-32) (2413824*S-43104*w-39) k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((314048*S-5608*w-9),(3041920*S-54320*w-55)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (628096*S-11216*w-22) := by omega
      have hy : c+4 = (3041920*S-54320*w-51) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1074528*S-19188*w-23),(1520960*S-27160*w-29)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2149056*S-38376*w-50) := by omega
      have hy : c+4 = (1520960*S-27160*w-25) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1454768*S-25978*w-30),(760480*S-13580*w-16)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2909536*S-51956*w-64) := by omega
      have hy : c+4 = (760480*S-13580*w-12) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (2909536*S-51956*w-64) hP (by omega) (by omega)

private theorem block_L0_1_1_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (1204224*S-21504*w-28) (2465792*S-44032*w-33) := by
  have h0 : inverseAt (1204224*S-21504*w-28) (2465792*S-44032*w-33) 0 = some ((301056*S-5376*w-8),(3067904*S-54784*w-47)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (1204224*S-21504*w-28) (2465792*S-44032*w-33) 1 = some ((1068032*S-19072*w-20),(1533952*S-27392*w-25)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (3067904*S-54784*w-47) ∧ (3067904*S-54784*w-47)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (1204224*S-21504*w-28) (2465792*S-44032*w-33) 2 = some ((1451520*S-25920*w-26),(766976*S-13696*w-14)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1533952*S-27392*w-25) ∧ (1533952*S-27392*w-25)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((2465792*S-44032*w-33)+(1204224*S-21504*w-28)/2+3)%2^(2+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1204224*S-21504*w-28) (2465792*S-44032*w-33) k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((301056*S-5376*w-8),(3067904*S-54784*w-47)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1068032*S-19072*w-20),(1533952*S-27392*w-25)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1451520*S-25920*w-26),(766976*S-13696*w-14)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1204224*S-21504*w-28) (2465792*S-44032*w-33) k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((301056*S-5376*w-8),(3067904*S-54784*w-47)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (602112*S-10752*w-20) := by omega
      have hy : c+4 = (3067904*S-54784*w-43) := by omega
      rw [hx,hy]
      exact block_L0_1_1_0_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1068032*S-19072*w-20),(1533952*S-27392*w-25)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2136064*S-38144*w-44) := by omega
      have hy : c+4 = (1533952*S-27392*w-21) := by omega
      rw [hx,hy]
      exact block_L0_1_1_0_1_ S w hS hP
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1451520*S-25920*w-26),(766976*S-13696*w-14)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2903040*S-51840*w-56) := by omega
      have hy : c+4 = (766976*S-13696*w-10) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (2903040*S-51840*w-56) hP (by omega) (by omega)

private theorem block_L0_1_3_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (1677312*S-29952*w-36) (1992704*S-35584*w-29) := by
  have h0 : inverseAt (1677312*S-29952*w-36) (1992704*S-35584*w-29) 0 = some ((419328*S-7488*w-10),(2831360*S-50560*w-47)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (1677312*S-29952*w-36) (1992704*S-35584*w-29) 1 = some ((1127168*S-20128*w-22),(1415680*S-25280*w-25)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2831360*S-50560*w-47) ∧ (2831360*S-50560*w-47)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (1677312*S-29952*w-36) (1992704*S-35584*w-29) 2 = some ((1481088*S-26448*w-28),(707840*S-12640*w-14)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1415680*S-25280*w-25) ∧ (1415680*S-25280*w-25)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((1992704*S-35584*w-29)+(1677312*S-29952*w-36)/2+3)%2^(2+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1677312*S-29952*w-36) (1992704*S-35584*w-29) k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((419328*S-7488*w-10),(2831360*S-50560*w-47)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1127168*S-20128*w-22),(1415680*S-25280*w-25)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1481088*S-26448*w-28),(707840*S-12640*w-14)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1677312*S-29952*w-36) (1992704*S-35584*w-29) k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((419328*S-7488*w-10),(2831360*S-50560*w-47)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (838656*S-14976*w-24) := by omega
      have hy : c+4 = (2831360*S-50560*w-43) := by omega
      rw [hx,hy]
      exact block_L0_1_3_0_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1127168*S-20128*w-22),(1415680*S-25280*w-25)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2254336*S-40256*w-48) := by omega
      have hy : c+4 = (1415680*S-25280*w-21) := by omega
      rw [hx,hy]
      exact block_L0_1_3_0_1_ S w hS hP
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1481088*S-26448*w-28),(707840*S-12640*w-14)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2962176*S-52896*w-60) := by omega
      have hy : c+4 = (707840*S-12640*w-10) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (2962176*S-52896*w-60) hP (by omega) (by omega)

private theorem block_L0_4_0_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (874496*S-15616*w-24) (2795520*S-49920*w-41) := by
  have h0 : inverseAt (874496*S-15616*w-24) (2795520*S-49920*w-41) 0 = some ((218624*S-3904*w-7),(3232768*S-57728*w-53)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (874496*S-15616*w-24) (2795520*S-49920*w-41) 1 = some ((1026816*S-18336*w-20),(1616384*S-28864*w-28)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (3232768*S-57728*w-53) ∧ (3232768*S-57728*w-53)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((2795520*S-49920*w-41)+(874496*S-15616*w-24)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (874496*S-15616*w-24) (2795520*S-49920*w-41) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((218624*S-3904*w-7),(3232768*S-57728*w-53)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1026816*S-18336*w-20),(1616384*S-28864*w-28)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (874496*S-15616*w-24) (2795520*S-49920*w-41) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((218624*S-3904*w-7),(3232768*S-57728*w-53)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (437248*S-7808*w-18) := by omega
      have hy : c+4 = (3232768*S-57728*w-49) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1026816*S-18336*w-20),(1616384*S-28864*w-28)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2053632*S-36672*w-44) := by omega
      have hy : c+4 = (1616384*S-28864*w-24) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (2053632*S-36672*w-44) hP (by omega) (by omega)

private theorem block_L0_4_1_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (1354752*S-24192*w-32) (2315264*S-41344*w-35) := by
  have h0 : inverseAt (1354752*S-24192*w-32) (2315264*S-41344*w-35) 0 = some ((338688*S-6048*w-9),(2992640*S-53440*w-51)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (1354752*S-24192*w-32) (2315264*S-41344*w-35) 1 = some ((1086848*S-19408*w-22),(1496320*S-26720*w-27)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2992640*S-53440*w-51) ∧ (2992640*S-53440*w-51)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (1354752*S-24192*w-32) (2315264*S-41344*w-35) 2 = some ((1460928*S-26088*w-29),(748160*S-13360*w-15)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1496320*S-26720*w-27) ∧ (1496320*S-26720*w-27)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h3 : inverseAt (1354752*S-24192*w-32) (2315264*S-41344*w-35) 3 = some ((1647968*S-29428*w-33),(374080*S-6680*w-9)) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ (748160*S-13360*w-15) ∧ (748160*S-13360*w-15)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h4 : inverseAt (1354752*S-24192*w-32) (2315264*S-41344*w-35) 4 = some ((1741488*S-31098*w-35),(187040*S-3340*w-6)) := by
    rw [inverseAt, h3]
    have hc : 3 ≤ (374080*S-6680*w-9) ∧ (374080*S-6680*w-9)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((2315264*S-41344*w-35)+(1354752*S-24192*w-32)/2+3)%2^(4+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1354752*S-24192*w-32) (2315264*S-41344*w-35) k 1 4 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((338688*S-6048*w-9),(2992640*S-53440*w-51)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1086848*S-19408*w-22),(1496320*S-26720*w-27)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1460928*S-26088*w-29),(748160*S-13360*w-15)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=((1647968*S-29428*w-33),(374080*S-6680*w-9)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h4] at hval
      have hp : (k,1)=((1741488*S-31098*w-35),(187040*S-3340*w-6)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1354752*S-24192*w-32) (2315264*S-41344*w-35) k c 4 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((338688*S-6048*w-9),(2992640*S-53440*w-51)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (677376*S-12096*w-22) := by omega
      have hy : c+4 = (2992640*S-53440*w-47) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1086848*S-19408*w-22),(1496320*S-26720*w-27)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2173696*S-38816*w-48) := by omega
      have hy : c+4 = (1496320*S-26720*w-23) := by omega
      rw [hx,hy]
      exact block_L0_4_1_0_1_ S w hS hP
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1460928*S-26088*w-29),(748160*S-13360*w-15)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2921856*S-52176*w-62) := by omega
      have hy : c+4 = (748160*S-13360*w-11) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h3] at hval
      have hp : (k,c)=((1647968*S-29428*w-33),(374080*S-6680*w-9)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3295936*S-58856*w-70) := by omega
      have hy : c+4 = (374080*S-6680*w-5) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h4] at hval
      have hp : (k,c)=((1741488*S-31098*w-35),(187040*S-3340*w-6)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3482976*S-62196*w-74) := by omega
      have hy : c+4 = (187040*S-3340*w-2) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_4_1_1_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (2512384*S-44864*w-52) (1157632*S-20672*w-17) := by
  have h0 : inverseAt (2512384*S-44864*w-52) (1157632*S-20672*w-17) 0 = some ((628096*S-11216*w-14),(2413824*S-43104*w-43)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (2512384*S-44864*w-52) (1157632*S-20672*w-17) 1 = some ((1231552*S-21992*w-25),(1206912*S-21552*w-23)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2413824*S-43104*w-43) ∧ (2413824*S-43104*w-43)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (2512384*S-44864*w-52) (1157632*S-20672*w-17) 2 = some ((1533280*S-27380*w-31),(603456*S-10776*w-13)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1206912*S-21552*w-23) ∧ (1206912*S-21552*w-23)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h3 : inverseAt (2512384*S-44864*w-52) (1157632*S-20672*w-17) 3 = some ((1684144*S-30074*w-34),(301728*S-5388*w-8)) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ (603456*S-10776*w-13) ∧ (603456*S-10776*w-13)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((1157632*S-20672*w-17)+(2512384*S-44864*w-52)/2+3)%2^(3+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2512384*S-44864*w-52) (1157632*S-20672*w-17) k 1 3 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((628096*S-11216*w-14),(2413824*S-43104*w-43)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1231552*S-21992*w-25),(1206912*S-21552*w-23)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1533280*S-27380*w-31),(603456*S-10776*w-13)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=((1684144*S-30074*w-34),(301728*S-5388*w-8)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2512384*S-44864*w-52) (1157632*S-20672*w-17) k c 3 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((628096*S-11216*w-14),(2413824*S-43104*w-43)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1256192*S-22432*w-32) := by omega
      have hy : c+4 = (2413824*S-43104*w-39) := by omega
      rw [hx,hy]
      exact block_L0_4_1_1_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1231552*S-21992*w-25),(1206912*S-21552*w-23)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2463104*S-43984*w-54) := by omega
      have hy : c+4 = (1206912*S-21552*w-19) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1533280*S-27380*w-31),(603456*S-10776*w-13)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3066560*S-54760*w-66) := by omega
      have hy : c+4 = (603456*S-10776*w-9) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h3] at hval
      have hp : (k,c)=((1684144*S-30074*w-34),(301728*S-5388*w-8)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3368288*S-60148*w-72) := by omega
      have hy : c+4 = (301728*S-5388*w-4) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (3368288*S-60148*w-72) hP (by omega) (by omega)

private theorem block_L0_1_1_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (2408448*S-43008*w-44) (1261568*S-22528*w-15) := by
  have h0 : inverseAt (2408448*S-43008*w-44) (1261568*S-22528*w-15) 0 = some ((602112*S-10752*w-12),(2465792*S-44032*w-37)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (2408448*S-43008*w-44) (1261568*S-22528*w-15) 1 = some ((1218560*S-21760*w-21),(1232896*S-22016*w-20)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2465792*S-44032*w-37) ∧ (2465792*S-44032*w-37)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((1261568*S-22528*w-15)+(2408448*S-43008*w-44)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2408448*S-43008*w-44) (1261568*S-22528*w-15) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((602112*S-10752*w-12),(2465792*S-44032*w-37)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1218560*S-21760*w-21),(1232896*S-22016*w-20)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2408448*S-43008*w-44) (1261568*S-22528*w-15) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((602112*S-10752*w-12),(2465792*S-44032*w-37)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1204224*S-21504*w-28) := by omega
      have hy : c+4 = (2465792*S-44032*w-33) := by omega
      rw [hx,hy]
      exact block_L0_1_1_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1218560*S-21760*w-21),(1232896*S-22016*w-20)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2437120*S-43520*w-46) := by omega
      have hy : c+4 = (1232896*S-22016*w-16) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_1_3_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (3354624*S-59904*w-60) (315392*S-5632*w-3) := by
  have h0 : inverseAt (3354624*S-59904*w-60) (315392*S-5632*w-3) 0 = some ((838656*S-14976*w-16),(1992704*S-35584*w-33)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (3354624*S-59904*w-60) (315392*S-5632*w-3) 1 = some ((1336832*S-23872*w-24),(996352*S-17792*w-18)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (1992704*S-35584*w-33) ∧ (1992704*S-35584*w-33)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((315392*S-5632*w-3)+(3354624*S-59904*w-60)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (3354624*S-59904*w-60) (315392*S-5632*w-3) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((838656*S-14976*w-16),(1992704*S-35584*w-33)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1336832*S-23872*w-24),(996352*S-17792*w-18)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (3354624*S-59904*w-60) (315392*S-5632*w-3) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((838656*S-14976*w-16),(1992704*S-35584*w-33)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1677312*S-29952*w-36) := by omega
      have hy : c+4 = (1992704*S-35584*w-29) := by omega
      rw [hx,hy]
      exact block_L0_1_3_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1336832*S-23872*w-24),(996352*S-17792*w-18)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2673664*S-47744*w-52) := by omega
      have hy : c+4 = (996352*S-17792*w-14) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (2673664*S-47744*w-52) hP (by omega) (by omega)

private theorem block_L0_1_4_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (3512320*S-62720*w-64) (157696*S-2816*w-1) := by
  have h0 : inverseAt (3512320*S-62720*w-64) (157696*S-2816*w-1) 0 = some ((878080*S-15680*w-17),(1913856*S-34176*w-33)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (3512320*S-62720*w-64) (157696*S-2816*w-1) 1 = some ((1356544*S-24224*w-25),(956928*S-17088*w-18)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (1913856*S-34176*w-33) ∧ (1913856*S-34176*w-33)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((157696*S-2816*w-1)+(3512320*S-62720*w-64)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (3512320*S-62720*w-64) (157696*S-2816*w-1) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((878080*S-15680*w-17),(1913856*S-34176*w-33)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1356544*S-24224*w-25),(956928*S-17088*w-18)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (3512320*S-62720*w-64) (157696*S-2816*w-1) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((878080*S-15680*w-17),(1913856*S-34176*w-33)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1756160*S-31360*w-38) := by omega
      have hy : c+4 = (1913856*S-34176*w-29) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1356544*S-24224*w-25),(956928*S-17088*w-18)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2713088*S-48448*w-54) := by omega
      have hy : c+4 = (956928*S-17088*w-14) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_4_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (1748992*S-31232*w-36) (1921024*S-34304*w-27) := by
  have h0 : inverseAt (1748992*S-31232*w-36) (1921024*S-34304*w-27) 0 = some ((437248*S-7808*w-10),(2795520*S-49920*w-45)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (1748992*S-31232*w-36) (1921024*S-34304*w-27) 1 = some ((1136128*S-20288*w-21),(1397760*S-24960*w-24)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2795520*S-49920*w-45) ∧ (2795520*S-49920*w-45)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((1921024*S-34304*w-27)+(1748992*S-31232*w-36)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1748992*S-31232*w-36) (1921024*S-34304*w-27) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((437248*S-7808*w-10),(2795520*S-49920*w-45)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1136128*S-20288*w-21),(1397760*S-24960*w-24)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1748992*S-31232*w-36) (1921024*S-34304*w-27) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((437248*S-7808*w-10),(2795520*S-49920*w-45)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (874496*S-15616*w-24) := by omega
      have hy : c+4 = (2795520*S-49920*w-41) := by omega
      rw [hx,hy]
      exact block_L0_4_0_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1136128*S-20288*w-21),(1397760*S-24960*w-24)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2272256*S-40576*w-46) := by omega
      have hy : c+4 = (1397760*S-24960*w-20) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_4_1_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (2709504*S-48384*w-52) (960512*S-17152*w-13) := by
  have h0 : inverseAt (2709504*S-48384*w-52) (960512*S-17152*w-13) 0 = some ((677376*S-12096*w-14),(2315264*S-41344*w-39)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (2709504*S-48384*w-52) (960512*S-17152*w-13) 1 = some ((1256192*S-22432*w-24),(1157632*S-20672*w-21)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2315264*S-41344*w-39) ∧ (2315264*S-41344*w-39)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (2709504*S-48384*w-52) (960512*S-17152*w-13) 2 = some ((1545600*S-27600*w-29),(578816*S-10336*w-12)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1157632*S-20672*w-21) ∧ (1157632*S-20672*w-21)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((960512*S-17152*w-13)+(2709504*S-48384*w-52)/2+3)%2^(2+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2709504*S-48384*w-52) (960512*S-17152*w-13) k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((677376*S-12096*w-14),(2315264*S-41344*w-39)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1256192*S-22432*w-24),(1157632*S-20672*w-21)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1545600*S-27600*w-29),(578816*S-10336*w-12)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2709504*S-48384*w-52) (960512*S-17152*w-13) k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((677376*S-12096*w-14),(2315264*S-41344*w-39)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1354752*S-24192*w-32) := by omega
      have hy : c+4 = (2315264*S-41344*w-35) := by omega
      rw [hx,hy]
      exact block_L0_4_1_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1256192*S-22432*w-24),(1157632*S-20672*w-21)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2512384*S-44864*w-52) := by omega
      have hy : c+4 = (1157632*S-20672*w-17) := by omega
      rw [hx,hy]
      exact block_L0_4_1_1_ S w hS hP
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1545600*S-27600*w-29),(578816*S-10336*w-12)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3091200*S-55200*w-62) := by omega
      have hy : c+4 = (578816*S-10336*w-8) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_1_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (2293760*S-40960*w-40) (1376256*S-24576*w-15) := by
  have h0 : inverseAt (2293760*S-40960*w-40) (1376256*S-24576*w-15) 0 = some ((573440*S-10240*w-11),(2523136*S-45056*w-35)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (2293760*S-40960*w-40) (1376256*S-24576*w-15) 1 = some ((1204224*S-21504*w-20),(1261568*S-22528*w-19)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2523136*S-45056*w-35) ∧ (2523136*S-45056*w-35)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (2293760*S-40960*w-40) (1376256*S-24576*w-15) 2 = some ((1519616*S-27136*w-25),(630784*S-11264*w-11)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1261568*S-22528*w-19) ∧ (1261568*S-22528*w-19)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h3 : inverseAt (2293760*S-40960*w-40) (1376256*S-24576*w-15) 3 = some ((1677312*S-29952*w-28),(315392*S-5632*w-7)) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ (630784*S-11264*w-11) ∧ (630784*S-11264*w-11)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h4 : inverseAt (2293760*S-40960*w-40) (1376256*S-24576*w-15) 4 = some ((1756160*S-31360*w-30),(157696*S-2816*w-5)) := by
    rw [inverseAt, h3]
    have hc : 3 ≤ (315392*S-5632*w-7) ∧ (315392*S-5632*w-7)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h5 : inverseAt (2293760*S-40960*w-40) (1376256*S-24576*w-15) 5 = some ((1795584*S-32064*w-31),(78848*S-1408*w-4)) := by
    rw [inverseAt, h4]
    have hc : 3 ≤ (157696*S-2816*w-5) ∧ (157696*S-2816*w-5)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((1376256*S-24576*w-15)+(2293760*S-40960*w-40)/2+3)%2^(5+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2293760*S-40960*w-40) (1376256*S-24576*w-15) k 1 5 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((573440*S-10240*w-11),(2523136*S-45056*w-35)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1204224*S-21504*w-20),(1261568*S-22528*w-19)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1519616*S-27136*w-25),(630784*S-11264*w-11)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=((1677312*S-29952*w-28),(315392*S-5632*w-7)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h4] at hval
      have hp : (k,1)=((1756160*S-31360*w-30),(157696*S-2816*w-5)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h5] at hval
      have hp : (k,1)=((1795584*S-32064*w-31),(78848*S-1408*w-4)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2293760*S-40960*w-40) (1376256*S-24576*w-15) k c 5 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((573440*S-10240*w-11),(2523136*S-45056*w-35)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1146880*S-20480*w-26) := by omega
      have hy : c+4 = (2523136*S-45056*w-31) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1204224*S-21504*w-20),(1261568*S-22528*w-19)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2408448*S-43008*w-44) := by omega
      have hy : c+4 = (1261568*S-22528*w-15) := by omega
      rw [hx,hy]
      exact block_L0_1_1_ S w hS hP
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1519616*S-27136*w-25),(630784*S-11264*w-11)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3039232*S-54272*w-54) := by omega
      have hy : c+4 = (630784*S-11264*w-7) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h3] at hval
      have hp : (k,c)=((1677312*S-29952*w-28),(315392*S-5632*w-7)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3354624*S-59904*w-60) := by omega
      have hy : c+4 = (315392*S-5632*w-3) := by omega
      rw [hx,hy]
      exact block_L0_1_3_ S w hS hP
    · subst t
      rw [h4] at hval
      have hp : (k,c)=((1756160*S-31360*w-30),(157696*S-2816*w-5)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3512320*S-62720*w-64) := by omega
      have hy : c+4 = (157696*S-2816*w-1) := by omega
      rw [hx,hy]
      exact block_L0_1_4_ S w hS hP
    · subst t
      rw [h5] at hval
      have hp : (k,c)=((1795584*S-32064*w-31),(78848*S-1408*w-4)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3591168*S-64128*w-66) := by omega
      have hy : c+4 = (78848*S-1408*w) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_3_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (3325952*S-59392*w-56) (344064*S-6144*w-3) := by
  have h0 : inverseAt (3325952*S-59392*w-56) (344064*S-6144*w-3) 0 = some ((831488*S-14848*w-15),(2007040*S-35840*w-31)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (3325952*S-59392*w-56) (344064*S-6144*w-3) 1 = some ((1333248*S-23808*w-23),(1003520*S-17920*w-17)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2007040*S-35840*w-31) ∧ (2007040*S-35840*w-31)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (3325952*S-59392*w-56) (344064*S-6144*w-3) 2 = some ((1584128*S-28288*w-27),(501760*S-8960*w-10)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1003520*S-17920*w-17) ∧ (1003520*S-17920*w-17)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((344064*S-6144*w-3)+(3325952*S-59392*w-56)/2+3)%2^(2+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (3325952*S-59392*w-56) (344064*S-6144*w-3) k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((831488*S-14848*w-15),(2007040*S-35840*w-31)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1333248*S-23808*w-23),(1003520*S-17920*w-17)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1584128*S-28288*w-27),(501760*S-8960*w-10)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (3325952*S-59392*w-56) (344064*S-6144*w-3) k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((831488*S-14848*w-15),(2007040*S-35840*w-31)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1662976*S-29696*w-34) := by omega
      have hy : c+4 = (2007040*S-35840*w-27) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1333248*S-23808*w-23),(1003520*S-17920*w-17)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2666496*S-47616*w-50) := by omega
      have hy : c+4 = (1003520*S-17920*w-13) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1584128*S-28288*w-27),(501760*S-8960*w-10)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3168256*S-56576*w-58) := by omega
      have hy : c+4 = (501760*S-8960*w-6) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_4_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (3497984*S-62464*w-60) (172032*S-3072*w-1) := by
  have h0 : inverseAt (3497984*S-62464*w-60) (172032*S-3072*w-1) 0 = some ((874496*S-15616*w-16),(1921024*S-34304*w-31)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (3497984*S-62464*w-60) (172032*S-3072*w-1) 1 = some ((1354752*S-24192*w-24),(960512*S-17152*w-17)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (1921024*S-34304*w-31) ∧ (1921024*S-34304*w-31)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (3497984*S-62464*w-60) (172032*S-3072*w-1) 2 = some ((1594880*S-28480*w-28),(480256*S-8576*w-10)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (960512*S-17152*w-17) ∧ (960512*S-17152*w-17)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((172032*S-3072*w-1)+(3497984*S-62464*w-60)/2+3)%2^(2+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (3497984*S-62464*w-60) (172032*S-3072*w-1) k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((874496*S-15616*w-16),(1921024*S-34304*w-31)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1354752*S-24192*w-24),(960512*S-17152*w-17)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1594880*S-28480*w-28),(480256*S-8576*w-10)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (3497984*S-62464*w-60) (172032*S-3072*w-1) k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((874496*S-15616*w-16),(1921024*S-34304*w-31)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1748992*S-31232*w-36) := by omega
      have hy : c+4 = (1921024*S-34304*w-27) := by omega
      rw [hx,hy]
      exact block_L0_4_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1354752*S-24192*w-24),(960512*S-17152*w-17)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2709504*S-48384*w-52) := by omega
      have hy : c+4 = (960512*S-17152*w-13) := by omega
      rw [hx,hy]
      exact block_L0_4_1_ S w hS hP
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1594880*S-28480*w-28),(480256*S-8576*w-10)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3189760*S-56960*w-60) := by omega
      have hy : c+4 = (480256*S-8576*w-6) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (3189760*S-56960*w-60) hP (by omega) (by omega)

private theorem block_L0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (1835008*S-32768*w-32) (1835008*S-32768*w-19) := by
  have h0 : inverseAt (1835008*S-32768*w-32) (1835008*S-32768*w-19) 0 = some ((458752*S-8192*w-9),(2752512*S-49152*w-35)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (1835008*S-32768*w-32) (1835008*S-32768*w-19) 1 = some ((1146880*S-20480*w-18),(1376256*S-24576*w-19)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2752512*S-49152*w-35) ∧ (2752512*S-49152*w-35)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (1835008*S-32768*w-32) (1835008*S-32768*w-19) 2 = some ((1490944*S-26624*w-23),(688128*S-12288*w-11)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1376256*S-24576*w-19) ∧ (1376256*S-24576*w-19)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h3 : inverseAt (1835008*S-32768*w-32) (1835008*S-32768*w-19) 3 = some ((1662976*S-29696*w-26),(344064*S-6144*w-7)) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ (688128*S-12288*w-11) ∧ (688128*S-12288*w-11)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h4 : inverseAt (1835008*S-32768*w-32) (1835008*S-32768*w-19) 4 = some ((1748992*S-31232*w-28),(172032*S-3072*w-5)) := by
    rw [inverseAt, h3]
    have hc : 3 ≤ (344064*S-6144*w-7) ∧ (344064*S-6144*w-7)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h5 : inverseAt (1835008*S-32768*w-32) (1835008*S-32768*w-19) 5 = some ((1792000*S-32000*w-29),(86016*S-1536*w-4)) := by
    rw [inverseAt, h4]
    have hc : 3 ≤ (172032*S-3072*w-5) ∧ (172032*S-3072*w-5)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((1835008*S-32768*w-19)+(1835008*S-32768*w-32)/2+3)%2^(5+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1835008*S-32768*w-32) (1835008*S-32768*w-19) k 1 5 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((458752*S-8192*w-9),(2752512*S-49152*w-35)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1146880*S-20480*w-18),(1376256*S-24576*w-19)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1490944*S-26624*w-23),(688128*S-12288*w-11)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=((1662976*S-29696*w-26),(344064*S-6144*w-7)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h4] at hval
      have hp : (k,1)=((1748992*S-31232*w-28),(172032*S-3072*w-5)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h5] at hval
      have hp : (k,1)=((1792000*S-32000*w-29),(86016*S-1536*w-4)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1835008*S-32768*w-32) (1835008*S-32768*w-19) k c 5 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((458752*S-8192*w-9),(2752512*S-49152*w-35)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (917504*S-16384*w-22) := by omega
      have hy : c+4 = (2752512*S-49152*w-31) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1146880*S-20480*w-18),(1376256*S-24576*w-19)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2293760*S-40960*w-40) := by omega
      have hy : c+4 = (1376256*S-24576*w-15) := by omega
      rw [hx,hy]
      exact block_L0_1_ S w hS hP
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1490944*S-26624*w-23),(688128*S-12288*w-11)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2981888*S-53248*w-50) := by omega
      have hy : c+4 = (688128*S-12288*w-7) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h3] at hval
      have hp : (k,c)=((1662976*S-29696*w-26),(344064*S-6144*w-7)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3325952*S-59392*w-56) := by omega
      have hy : c+4 = (344064*S-6144*w-3) := by omega
      rw [hx,hy]
      exact block_L0_3_ S w hS hP
    · subst t
      rw [h4] at hval
      have hp : (k,c)=((1748992*S-31232*w-28),(172032*S-3072*w-5)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3497984*S-62464*w-60) := by omega
      have hy : c+4 = (172032*S-3072*w-1) := by omega
      rw [hx,hy]
      exact block_L0_4_ S w hS hP
    · subst t
      rw [h5] at hval
      have hp : (k,c)=((1792000*S-32000*w-29),(86016*S-1536*w-4)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3584000*S-64000*w-62) := by omega
      have hy : c+4 = (86016*S-1536*w) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

theorem root0_blocked (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (1835008*S-32768*w-32) (1835008*S-32768*w-19) :=
  block_L0_ S w hS hP

private theorem block_L1_0_0_0_1_1_1_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (1206912*S-21552*w-32) (2463104*S-43984*w-41) := by
  have h0 : inverseAt (1206912*S-21552*w-32) (2463104*S-43984*w-41) 0 = some ((301728*S-5388*w-9),(3066560*S-54760*w-57)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (1206912*S-21552*w-32) (2463104*S-43984*w-41) 1 = some ((1068368*S-19078*w-23),(1533280*S-27380*w-30)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (3066560*S-54760*w-57) ∧ (3066560*S-54760*w-57)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((2463104*S-43984*w-41)+(1206912*S-21552*w-32)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1206912*S-21552*w-32) (2463104*S-43984*w-41) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((301728*S-5388*w-9),(3066560*S-54760*w-57)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1068368*S-19078*w-23),(1533280*S-27380*w-30)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1206912*S-21552*w-32) (2463104*S-43984*w-41) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((301728*S-5388*w-9),(3066560*S-54760*w-57)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (603456*S-10776*w-22) := by omega
      have hy : c+4 = (3066560*S-54760*w-53) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1068368*S-19078*w-23),(1533280*S-27380*w-30)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2136736*S-38156*w-50) := by omega
      have hy : c+4 = (1533280*S-27380*w-26) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_0_0_0_1_2_0_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (748160*S-13360*w-24) (2921856*S-52176*w-49) := by
  have h0 : inverseAt (748160*S-13360*w-24) (2921856*S-52176*w-49) 0 = some ((187040*S-3340*w-7),(3295936*S-58856*w-61)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (748160*S-13360*w-24) (2921856*S-52176*w-49) 1 = some ((1011024*S-18054*w-22),(1647968*S-29428*w-32)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (3295936*S-58856*w-61) ∧ (3295936*S-58856*w-61)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((2921856*S-52176*w-49)+(748160*S-13360*w-24)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (748160*S-13360*w-24) (2921856*S-52176*w-49) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((187040*S-3340*w-7),(3295936*S-58856*w-61)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1011024*S-18054*w-22),(1647968*S-29428*w-32)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (748160*S-13360*w-24) (2921856*S-52176*w-49) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((187040*S-3340*w-7),(3295936*S-58856*w-61)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (374080*S-6680*w-18) := by omega
      have hy : c+4 = (3295936*S-58856*w-57) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1011024*S-18054*w-22),(1647968*S-29428*w-32)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2022048*S-36108*w-48) := by omega
      have hy : c+4 = (1647968*S-29428*w-28) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (2022048*S-36108*w-48) hP (by omega) (by omega)

private theorem block_L1_0_0_0_1_1_1_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (2413824*S-43104*w-52) (1256192*S-22432*w-19) := by
  have h0 : inverseAt (2413824*S-43104*w-52) (1256192*S-22432*w-19) 0 = some ((603456*S-10776*w-14),(2463104*S-43984*w-45)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (2413824*S-43104*w-52) (1256192*S-22432*w-19) 1 = some ((1219232*S-21772*w-25),(1231552*S-21992*w-24)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2463104*S-43984*w-45) ∧ (2463104*S-43984*w-45)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((1256192*S-22432*w-19)+(2413824*S-43104*w-52)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2413824*S-43104*w-52) (1256192*S-22432*w-19) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((603456*S-10776*w-14),(2463104*S-43984*w-45)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1219232*S-21772*w-25),(1231552*S-21992*w-24)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2413824*S-43104*w-52) (1256192*S-22432*w-19) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((603456*S-10776*w-14),(2463104*S-43984*w-45)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1206912*S-21552*w-32) := by omega
      have hy : c+4 = (2463104*S-43984*w-41) := by omega
      rw [hx,hy]
      exact block_L1_0_0_0_1_1_1_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1219232*S-21772*w-25),(1231552*S-21992*w-24)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2438464*S-43544*w-54) := by omega
      have hy : c+4 = (1231552*S-21992*w-20) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_0_0_0_1_1_2_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (3041920*S-54320*w-64) (628096*S-11216*w-9) := by
  have h0 : inverseAt (3041920*S-54320*w-64) (628096*S-11216*w-9) 0 = some ((760480*S-13580*w-17),(2149056*S-38376*w-41)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (3041920*S-54320*w-64) (628096*S-11216*w-9) 1 = some ((1297744*S-23174*w-27),(1074528*S-19188*w-22)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2149056*S-38376*w-41) ∧ (2149056*S-38376*w-41)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((628096*S-11216*w-9)+(3041920*S-54320*w-64)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (3041920*S-54320*w-64) (628096*S-11216*w-9) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((760480*S-13580*w-17),(2149056*S-38376*w-41)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1297744*S-23174*w-27),(1074528*S-19188*w-22)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (3041920*S-54320*w-64) (628096*S-11216*w-9) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((760480*S-13580*w-17),(2149056*S-38376*w-41)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1520960*S-27160*w-38) := by omega
      have hy : c+4 = (2149056*S-38376*w-37) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1297744*S-23174*w-27),(1074528*S-19188*w-22)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2595488*S-46348*w-58) := by omega
      have hy : c+4 = (1074528*S-19188*w-18) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_0_0_0_1_2_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (1496320*S-26720*w-36) (2173696*S-38816*w-35) := by
  have h0 : inverseAt (1496320*S-26720*w-36) (2173696*S-38816*w-35) 0 = some ((374080*S-6680*w-10),(2921856*S-52176*w-53)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (1496320*S-26720*w-36) (2173696*S-38816*w-35) 1 = some ((1104544*S-19724*w-23),(1460928*S-26088*w-28)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2921856*S-52176*w-53) ∧ (2921856*S-52176*w-53)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((2173696*S-38816*w-35)+(1496320*S-26720*w-36)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1496320*S-26720*w-36) (2173696*S-38816*w-35) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((374080*S-6680*w-10),(2921856*S-52176*w-53)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1104544*S-19724*w-23),(1460928*S-26088*w-28)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1496320*S-26720*w-36) (2173696*S-38816*w-35) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((374080*S-6680*w-10),(2921856*S-52176*w-53)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (748160*S-13360*w-24) := by omega
      have hy : c+4 = (2921856*S-52176*w-49) := by omega
      rw [hx,hy]
      exact block_L1_0_0_0_1_2_0_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1104544*S-19724*w-23),(1460928*S-26088*w-28)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2209088*S-39448*w-50) := by omega
      have hy : c+4 = (1460928*S-26088*w-24) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_0_0_0_1_2_1_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (2583168*S-46128*w-56) (1086848*S-19408*w-17) := by
  have h0 : inverseAt (2583168*S-46128*w-56) (1086848*S-19408*w-17) 0 = some ((645792*S-11532*w-15),(2378432*S-42472*w-45)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (2583168*S-46128*w-56) (1086848*S-19408*w-17) 1 = some ((1240400*S-22150*w-26),(1189216*S-21236*w-24)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2378432*S-42472*w-45) ∧ (2378432*S-42472*w-45)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((1086848*S-19408*w-17)+(2583168*S-46128*w-56)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2583168*S-46128*w-56) (1086848*S-19408*w-17) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((645792*S-11532*w-15),(2378432*S-42472*w-45)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1240400*S-22150*w-26),(1189216*S-21236*w-24)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2583168*S-46128*w-56) (1086848*S-19408*w-17) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((645792*S-11532*w-15),(2378432*S-42472*w-45)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1291584*S-23064*w-34) := by omega
      have hy : c+4 = (2378432*S-42472*w-41) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1240400*S-22150*w-26),(1189216*S-21236*w-24)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2480800*S-44300*w-56) := by omega
      have hy : c+4 = (1189216*S-21236*w-20) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (2480800*S-44300*w-56) hP (by omega) (by omega)

private theorem block_L1_0_0_0_1_1_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (2315264*S-41344*w-48) (1354752*S-24192*w-19) := by
  have h0 : inverseAt (2315264*S-41344*w-48) (1354752*S-24192*w-19) 0 = some ((578816*S-10336*w-13),(2512384*S-44864*w-43)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (2315264*S-41344*w-48) (1354752*S-24192*w-19) 1 = some ((1206912*S-21552*w-24),(1256192*S-22432*w-23)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2512384*S-44864*w-43) ∧ (2512384*S-44864*w-43)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (2315264*S-41344*w-48) (1354752*S-24192*w-19) 2 = some ((1520960*S-27160*w-30),(628096*S-11216*w-13)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1256192*S-22432*w-23) ∧ (1256192*S-22432*w-23)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h3 : inverseAt (2315264*S-41344*w-48) (1354752*S-24192*w-19) 3 = some ((1677984*S-29964*w-33),(314048*S-5608*w-8)) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ (628096*S-11216*w-13) ∧ (628096*S-11216*w-13)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((1354752*S-24192*w-19)+(2315264*S-41344*w-48)/2+3)%2^(3+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2315264*S-41344*w-48) (1354752*S-24192*w-19) k 1 3 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((578816*S-10336*w-13),(2512384*S-44864*w-43)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1206912*S-21552*w-24),(1256192*S-22432*w-23)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1520960*S-27160*w-30),(628096*S-11216*w-13)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=((1677984*S-29964*w-33),(314048*S-5608*w-8)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2315264*S-41344*w-48) (1354752*S-24192*w-19) k c 3 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((578816*S-10336*w-13),(2512384*S-44864*w-43)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1157632*S-20672*w-30) := by omega
      have hy : c+4 = (2512384*S-44864*w-39) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1206912*S-21552*w-24),(1256192*S-22432*w-23)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2413824*S-43104*w-52) := by omega
      have hy : c+4 = (1256192*S-22432*w-19) := by omega
      rw [hx,hy]
      exact block_L1_0_0_0_1_1_1_ S w hS hP
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1520960*S-27160*w-30),(628096*S-11216*w-13)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3041920*S-54320*w-64) := by omega
      have hy : c+4 = (628096*S-11216*w-9) := by omega
      rw [hx,hy]
      exact block_L1_0_0_0_1_1_2_ S w hS hP
    · subst t
      rw [h3] at hval
      have hp : (k,c)=((1677984*S-29964*w-33),(314048*S-5608*w-8)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3355968*S-59928*w-70) := by omega
      have hy : c+4 = (314048*S-5608*w-4) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_0_0_0_1_2_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (2992640*S-53440*w-60) (677376*S-12096*w-9) := by
  have h0 : inverseAt (2992640*S-53440*w-60) (677376*S-12096*w-9) 0 = some ((748160*S-13360*w-16),(2173696*S-38816*w-39)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (2992640*S-53440*w-60) (677376*S-12096*w-9) 1 = some ((1291584*S-23064*w-26),(1086848*S-19408*w-21)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2173696*S-38816*w-39) ∧ (2173696*S-38816*w-39)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (2992640*S-53440*w-60) (677376*S-12096*w-9) 2 = some ((1563296*S-27916*w-31),(543424*S-9704*w-12)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1086848*S-19408*w-21) ∧ (1086848*S-19408*w-21)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((677376*S-12096*w-9)+(2992640*S-53440*w-60)/2+3)%2^(2+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2992640*S-53440*w-60) (677376*S-12096*w-9) k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((748160*S-13360*w-16),(2173696*S-38816*w-39)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1291584*S-23064*w-26),(1086848*S-19408*w-21)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1563296*S-27916*w-31),(543424*S-9704*w-12)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2992640*S-53440*w-60) (677376*S-12096*w-9) k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((748160*S-13360*w-16),(2173696*S-38816*w-39)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1496320*S-26720*w-36) := by omega
      have hy : c+4 = (2173696*S-38816*w-35) := by omega
      rw [hx,hy]
      exact block_L1_0_0_0_1_2_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1291584*S-23064*w-26),(1086848*S-19408*w-21)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2583168*S-46128*w-56) := by omega
      have hy : c+4 = (1086848*S-19408*w-17) := by omega
      rw [hx,hy]
      exact block_L1_0_0_0_1_2_1_ S w hS hP
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1563296*S-27916*w-31),(543424*S-9704*w-12)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3126592*S-55832*w-66) := by omega
      have hy : c+4 = (543424*S-9704*w-8) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_0_0_0_1_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (1921024*S-34304*w-40) (1748992*S-31232*w-23) := by
  have h0 : inverseAt (1921024*S-34304*w-40) (1748992*S-31232*w-23) 0 = some ((480256*S-8576*w-11),(2709504*S-48384*w-43)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (1921024*S-34304*w-40) (1748992*S-31232*w-23) 1 = some ((1157632*S-20672*w-22),(1354752*S-24192*w-23)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2709504*S-48384*w-43) ∧ (2709504*S-48384*w-43)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (1921024*S-34304*w-40) (1748992*S-31232*w-23) 2 = some ((1496320*S-26720*w-28),(677376*S-12096*w-13)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1354752*S-24192*w-23) ∧ (1354752*S-24192*w-23)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h3 : inverseAt (1921024*S-34304*w-40) (1748992*S-31232*w-23) 3 = some ((1665664*S-29744*w-31),(338688*S-6048*w-8)) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ (677376*S-12096*w-13) ∧ (677376*S-12096*w-13)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((1748992*S-31232*w-23)+(1921024*S-34304*w-40)/2+3)%2^(3+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1921024*S-34304*w-40) (1748992*S-31232*w-23) k 1 3 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((480256*S-8576*w-11),(2709504*S-48384*w-43)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1157632*S-20672*w-22),(1354752*S-24192*w-23)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1496320*S-26720*w-28),(677376*S-12096*w-13)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=((1665664*S-29744*w-31),(338688*S-6048*w-8)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1921024*S-34304*w-40) (1748992*S-31232*w-23) k c 3 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((480256*S-8576*w-11),(2709504*S-48384*w-43)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (960512*S-17152*w-26) := by omega
      have hy : c+4 = (2709504*S-48384*w-39) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1157632*S-20672*w-22),(1354752*S-24192*w-23)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2315264*S-41344*w-48) := by omega
      have hy : c+4 = (1354752*S-24192*w-19) := by omega
      rw [hx,hy]
      exact block_L1_0_0_0_1_1_ S w hS hP
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1496320*S-26720*w-28),(677376*S-12096*w-13)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2992640*S-53440*w-60) := by omega
      have hy : c+4 = (677376*S-12096*w-9) := by omega
      rw [hx,hy]
      exact block_L1_0_0_0_1_2_ S w hS hP
    · subst t
      rw [h3] at hval
      have hp : (k,c)=((1665664*S-29744*w-31),(338688*S-6048*w-8)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3331328*S-59488*w-66) := by omega
      have hy : c+4 = (338688*S-6048*w-4) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_1_0_0_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (315392*S-5632*w-16) (3354624*S-59904*w-47) := by
  have h0 : inverseAt (315392*S-5632*w-16) (3354624*S-59904*w-47) 0 = some ((78848*S-1408*w-5),(3512320*S-62720*w-55)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (315392*S-5632*w-16) (3354624*S-59904*w-47) 1 = some ((956928*S-17088*w-19),(1756160*S-31360*w-29)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (3512320*S-62720*w-55) ∧ (3512320*S-62720*w-55)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (315392*S-5632*w-16) (3354624*S-59904*w-47) 2 = some ((1395968*S-24928*w-26),(878080*S-15680*w-16)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1756160*S-31360*w-29) ∧ (1756160*S-31360*w-29)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((3354624*S-59904*w-47)+(315392*S-5632*w-16)/2+3)%2^(2+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (315392*S-5632*w-16) (3354624*S-59904*w-47) k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((78848*S-1408*w-5),(3512320*S-62720*w-55)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((956928*S-17088*w-19),(1756160*S-31360*w-29)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1395968*S-24928*w-26),(878080*S-15680*w-16)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (315392*S-5632*w-16) (3354624*S-59904*w-47) k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((78848*S-1408*w-5),(3512320*S-62720*w-55)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (157696*S-2816*w-14) := by omega
      have hy : c+4 = (3512320*S-62720*w-51) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((956928*S-17088*w-19),(1756160*S-31360*w-29)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1913856*S-34176*w-42) := by omega
      have hy : c+4 = (1756160*S-31360*w-25) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1395968*S-24928*w-26),(878080*S-15680*w-16)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2791936*S-49856*w-56) := by omega
      have hy : c+4 = (878080*S-15680*w-12) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (2791936*S-49856*w-56) hP (by omega) (by omega)

private theorem block_L1_1_0_0_2_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (2831360*S-50560*w-56) (838656*S-14976*w-11) := by
  have h0 : inverseAt (2831360*S-50560*w-56) (838656*S-14976*w-11) 0 = some ((707840*S-12640*w-15),(2254336*S-40256*w-39)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (2831360*S-50560*w-56) (838656*S-14976*w-11) 1 = some ((1271424*S-22704*w-25),(1127168*S-20128*w-21)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2254336*S-40256*w-39) ∧ (2254336*S-40256*w-39)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (2831360*S-50560*w-56) (838656*S-14976*w-11) 2 = some ((1553216*S-27736*w-30),(563584*S-10064*w-12)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1127168*S-20128*w-21) ∧ (1127168*S-20128*w-21)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((838656*S-14976*w-11)+(2831360*S-50560*w-56)/2+3)%2^(2+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2831360*S-50560*w-56) (838656*S-14976*w-11) k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((707840*S-12640*w-15),(2254336*S-40256*w-39)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1271424*S-22704*w-25),(1127168*S-20128*w-21)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1553216*S-27736*w-30),(563584*S-10064*w-12)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2831360*S-50560*w-56) (838656*S-14976*w-11) k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((707840*S-12640*w-15),(2254336*S-40256*w-39)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1415680*S-25280*w-34) := by omega
      have hy : c+4 = (2254336*S-40256*w-35) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1271424*S-22704*w-25),(1127168*S-20128*w-21)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2542848*S-45408*w-54) := by omega
      have hy : c+4 = (1127168*S-20128*w-17) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1553216*S-27736*w-30),(563584*S-10064*w-12)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3106432*S-55472*w-64) := by omega
      have hy : c+4 = (563584*S-10064*w-8) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (3106432*S-55472*w-64) hP (by omega) (by omega)

private theorem block_L1_1_0_0_3_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (3250688*S-58048*w-64) (419328*S-7488*w-5) := by
  have h0 : inverseAt (3250688*S-58048*w-64) (419328*S-7488*w-5) 0 = some ((812672*S-14512*w-17),(2044672*S-36512*w-37)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (3250688*S-58048*w-64) (419328*S-7488*w-5) 1 = some ((1323840*S-23640*w-26),(1022336*S-18256*w-20)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2044672*S-36512*w-37) ∧ (2044672*S-36512*w-37)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((419328*S-7488*w-5)+(3250688*S-58048*w-64)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (3250688*S-58048*w-64) (419328*S-7488*w-5) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((812672*S-14512*w-17),(2044672*S-36512*w-37)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1323840*S-23640*w-26),(1022336*S-18256*w-20)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (3250688*S-58048*w-64) (419328*S-7488*w-5) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((812672*S-14512*w-17),(2044672*S-36512*w-37)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1625344*S-29024*w-38) := by omega
      have hy : c+4 = (2044672*S-36512*w-33) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1323840*S-23640*w-26),(1022336*S-18256*w-20)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2647680*S-47280*w-56) := by omega
      have hy : c+4 = (1022336*S-18256*w-16) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (2647680*S-47280*w-56) hP (by omega) (by omega)

private theorem block_L1_1_2_1_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (1300992*S-23232*w-32) (2369024*S-42304*w-37) := by
  have h0 : inverseAt (1300992*S-23232*w-32) (2369024*S-42304*w-37) 0 = some ((325248*S-5808*w-9),(3019520*S-53920*w-53)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (1300992*S-23232*w-32) (2369024*S-42304*w-37) 1 = some ((1080128*S-19288*w-22),(1509760*S-26960*w-28)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (3019520*S-53920*w-53) ∧ (3019520*S-53920*w-53)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((2369024*S-42304*w-37)+(1300992*S-23232*w-32)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1300992*S-23232*w-32) (2369024*S-42304*w-37) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((325248*S-5808*w-9),(3019520*S-53920*w-53)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1080128*S-19288*w-22),(1509760*S-26960*w-28)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1300992*S-23232*w-32) (2369024*S-42304*w-37) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((325248*S-5808*w-9),(3019520*S-53920*w-53)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (650496*S-11616*w-22) := by omega
      have hy : c+4 = (3019520*S-53920*w-49) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1080128*S-19288*w-22),(1509760*S-26960*w-28)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2160256*S-38576*w-48) := by omega
      have hy : c+4 = (1509760*S-26960*w-24) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (2160256*S-38576*w-48) hP (by omega) (by omega)

private theorem block_L1_1_2_3_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (1701504*S-30384*w-40) (1968512*S-35152*w-33) := by
  have h0 : inverseAt (1701504*S-30384*w-40) (1968512*S-35152*w-33) 0 = some ((425376*S-7596*w-11),(2819264*S-50344*w-53)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (1701504*S-30384*w-40) (1968512*S-35152*w-33) 1 = some ((1130192*S-20182*w-24),(1409632*S-25172*w-28)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2819264*S-50344*w-53) ∧ (2819264*S-50344*w-53)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((1968512*S-35152*w-33)+(1701504*S-30384*w-40)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1701504*S-30384*w-40) (1968512*S-35152*w-33) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((425376*S-7596*w-11),(2819264*S-50344*w-53)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1130192*S-20182*w-24),(1409632*S-25172*w-28)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1701504*S-30384*w-40) (1968512*S-35152*w-33) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((425376*S-7596*w-11),(2819264*S-50344*w-53)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (850752*S-15192*w-26) := by omega
      have hy : c+4 = (2819264*S-50344*w-49) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1130192*S-20182*w-24),(1409632*S-25172*w-28)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2260384*S-40364*w-52) := by omega
      have hy : c+4 = (1409632*S-25172*w-24) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (2260384*S-40364*w-52) hP (by omega) (by omega)

private theorem block_L1_0_0_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (344064*S-6144*w-16) (3325952*S-59392*w-43) := by
  have h0 : inverseAt (344064*S-6144*w-16) (3325952*S-59392*w-43) 0 = some ((86016*S-1536*w-5),(3497984*S-62464*w-51)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (344064*S-6144*w-16) (3325952*S-59392*w-43) 1 = some ((960512*S-17152*w-18),(1748992*S-31232*w-27)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (3497984*S-62464*w-51) ∧ (3497984*S-62464*w-51)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (344064*S-6144*w-16) (3325952*S-59392*w-43) 2 = some ((1397760*S-24960*w-25),(874496*S-15616*w-15)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1748992*S-31232*w-27) ∧ (1748992*S-31232*w-27)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h3 : inverseAt (344064*S-6144*w-16) (3325952*S-59392*w-43) 3 = some ((1616384*S-28864*w-29),(437248*S-7808*w-9)) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ (874496*S-15616*w-15) ∧ (874496*S-15616*w-15)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h4 : inverseAt (344064*S-6144*w-16) (3325952*S-59392*w-43) 4 = some ((1725696*S-30816*w-31),(218624*S-3904*w-6)) := by
    rw [inverseAt, h3]
    have hc : 3 ≤ (437248*S-7808*w-9) ∧ (437248*S-7808*w-9)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((3325952*S-59392*w-43)+(344064*S-6144*w-16)/2+3)%2^(4+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (344064*S-6144*w-16) (3325952*S-59392*w-43) k 1 4 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((86016*S-1536*w-5),(3497984*S-62464*w-51)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((960512*S-17152*w-18),(1748992*S-31232*w-27)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1397760*S-24960*w-25),(874496*S-15616*w-15)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=((1616384*S-28864*w-29),(437248*S-7808*w-9)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h4] at hval
      have hp : (k,1)=((1725696*S-30816*w-31),(218624*S-3904*w-6)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (344064*S-6144*w-16) (3325952*S-59392*w-43) k c 4 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((86016*S-1536*w-5),(3497984*S-62464*w-51)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (172032*S-3072*w-14) := by omega
      have hy : c+4 = (3497984*S-62464*w-47) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((960512*S-17152*w-18),(1748992*S-31232*w-27)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1921024*S-34304*w-40) := by omega
      have hy : c+4 = (1748992*S-31232*w-23) := by omega
      rw [hx,hy]
      exact block_L1_0_0_0_1_ S w hS hP
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1397760*S-24960*w-25),(874496*S-15616*w-15)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2795520*S-49920*w-54) := by omega
      have hy : c+4 = (874496*S-15616*w-11) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h3] at hval
      have hp : (k,c)=((1616384*S-28864*w-29),(437248*S-7808*w-9)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3232768*S-57728*w-62) := by omega
      have hy : c+4 = (437248*S-7808*w-5) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h4] at hval
      have hp : (k,c)=((1725696*S-30816*w-31),(218624*S-3904*w-6)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3451392*S-61632*w-66) := by omega
      have hy : c+4 = (218624*S-3904*w-2) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_0_0_1_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (2007040*S-35840*w-40) (1662976*S-29696*w-21) := by
  have h0 : inverseAt (2007040*S-35840*w-40) (1662976*S-29696*w-21) 0 = some ((501760*S-8960*w-11),(2666496*S-47616*w-41)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (2007040*S-35840*w-40) (1662976*S-29696*w-21) 1 = some ((1168384*S-20864*w-21),(1333248*S-23808*w-22)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2666496*S-47616*w-41) ∧ (2666496*S-47616*w-41)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((1662976*S-29696*w-21)+(2007040*S-35840*w-40)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2007040*S-35840*w-40) (1662976*S-29696*w-21) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((501760*S-8960*w-11),(2666496*S-47616*w-41)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1168384*S-20864*w-21),(1333248*S-23808*w-22)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2007040*S-35840*w-40) (1662976*S-29696*w-21) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((501760*S-8960*w-11),(2666496*S-47616*w-41)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1003520*S-17920*w-26) := by omega
      have hy : c+4 = (2666496*S-47616*w-37) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1168384*S-20864*w-21),(1333248*S-23808*w-22)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2336768*S-41728*w-46) := by omega
      have hy : c+4 = (1333248*S-23808*w-18) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_1_0_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (630784*S-11264*w-20) (3039232*S-54272*w-41) := by
  have h0 : inverseAt (630784*S-11264*w-20) (3039232*S-54272*w-41) 0 = some ((157696*S-2816*w-6),(3354624*S-59904*w-51)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (630784*S-11264*w-20) (3039232*S-54272*w-41) 1 = some ((996352*S-17792*w-19),(1677312*S-29952*w-27)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (3354624*S-59904*w-51) ∧ (3354624*S-59904*w-51)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (630784*S-11264*w-20) (3039232*S-54272*w-41) 2 = some ((1415680*S-25280*w-26),(838656*S-14976*w-15)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1677312*S-29952*w-27) ∧ (1677312*S-29952*w-27)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h3 : inverseAt (630784*S-11264*w-20) (3039232*S-54272*w-41) 3 = some ((1625344*S-29024*w-30),(419328*S-7488*w-9)) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ (838656*S-14976*w-15) ∧ (838656*S-14976*w-15)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h4 : inverseAt (630784*S-11264*w-20) (3039232*S-54272*w-41) 4 = some ((1730176*S-30896*w-32),(209664*S-3744*w-6)) := by
    rw [inverseAt, h3]
    have hc : 3 ≤ (419328*S-7488*w-9) ∧ (419328*S-7488*w-9)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((3039232*S-54272*w-41)+(630784*S-11264*w-20)/2+3)%2^(4+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (630784*S-11264*w-20) (3039232*S-54272*w-41) k 1 4 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((157696*S-2816*w-6),(3354624*S-59904*w-51)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((996352*S-17792*w-19),(1677312*S-29952*w-27)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1415680*S-25280*w-26),(838656*S-14976*w-15)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=((1625344*S-29024*w-30),(419328*S-7488*w-9)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h4] at hval
      have hp : (k,1)=((1730176*S-30896*w-32),(209664*S-3744*w-6)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (630784*S-11264*w-20) (3039232*S-54272*w-41) k c 4 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((157696*S-2816*w-6),(3354624*S-59904*w-51)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (315392*S-5632*w-16) := by omega
      have hy : c+4 = (3354624*S-59904*w-47) := by omega
      rw [hx,hy]
      exact block_L1_1_0_0_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((996352*S-17792*w-19),(1677312*S-29952*w-27)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1992704*S-35584*w-42) := by omega
      have hy : c+4 = (1677312*S-29952*w-23) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1415680*S-25280*w-26),(838656*S-14976*w-15)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2831360*S-50560*w-56) := by omega
      have hy : c+4 = (838656*S-14976*w-11) := by omega
      rw [hx,hy]
      exact block_L1_1_0_0_2_ S w hS hP
    · subst t
      rw [h3] at hval
      have hp : (k,c)=((1625344*S-29024*w-30),(419328*S-7488*w-9)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3250688*S-58048*w-64) := by omega
      have hy : c+4 = (419328*S-7488*w-5) := by omega
      rw [hx,hy]
      exact block_L1_1_0_0_3_ S w hS hP
    · subst t
      rw [h4] at hval
      have hp : (k,c)=((1730176*S-30896*w-32),(209664*S-3744*w-6)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3460352*S-61792*w-68) := by omega
      have hy : c+4 = (209664*S-3744*w-2) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (3460352*S-61792*w-68) hP (by omega) (by omega)

private theorem block_L1_1_2_1_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (2601984*S-46464*w-52) (1068032*S-19072*w-15) := by
  have h0 : inverseAt (2601984*S-46464*w-52) (1068032*S-19072*w-15) 0 = some ((650496*S-11616*w-14),(2369024*S-42304*w-41)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (2601984*S-46464*w-52) (1068032*S-19072*w-15) 1 = some ((1242752*S-22192*w-24),(1184512*S-21152*w-22)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2369024*S-42304*w-41) ∧ (2369024*S-42304*w-41)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((1068032*S-19072*w-15)+(2601984*S-46464*w-52)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2601984*S-46464*w-52) (1068032*S-19072*w-15) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((650496*S-11616*w-14),(2369024*S-42304*w-41)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1242752*S-22192*w-24),(1184512*S-21152*w-22)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2601984*S-46464*w-52) (1068032*S-19072*w-15) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((650496*S-11616*w-14),(2369024*S-42304*w-41)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1300992*S-23232*w-32) := by omega
      have hy : c+4 = (2369024*S-42304*w-37) := by omega
      rw [hx,hy]
      exact block_L1_1_2_1_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1242752*S-22192*w-24),(1184512*S-21152*w-22)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2485504*S-44384*w-52) := by omega
      have hy : c+4 = (1184512*S-21152*w-18) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (2485504*S-44384*w-52) hP (by omega) (by omega)

private theorem block_L1_1_2_3_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (3403008*S-60768*w-68) (267008*S-4768*w-3) := by
  have h0 : inverseAt (3403008*S-60768*w-68) (267008*S-4768*w-3) 0 = some ((850752*S-15192*w-18),(1968512*S-35152*w-37)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (3403008*S-60768*w-68) (267008*S-4768*w-3) 1 = some ((1342880*S-23980*w-27),(984256*S-17576*w-20)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (1968512*S-35152*w-37) ∧ (1968512*S-35152*w-37)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((267008*S-4768*w-3)+(3403008*S-60768*w-68)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (3403008*S-60768*w-68) (267008*S-4768*w-3) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((850752*S-15192*w-18),(1968512*S-35152*w-37)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1342880*S-23980*w-27),(984256*S-17576*w-20)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (3403008*S-60768*w-68) (267008*S-4768*w-3) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((850752*S-15192*w-18),(1968512*S-35152*w-37)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1701504*S-30384*w-40) := by omega
      have hy : c+4 = (1968512*S-35152*w-33) := by omega
      rw [hx,hy]
      exact block_L1_1_2_3_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1342880*S-23980*w-27),(984256*S-17576*w-20)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2685760*S-47960*w-58) := by omega
      have hy : c+4 = (984256*S-17576*w-16) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_1_2_4_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (3536512*S-63152*w-72) (133504*S-2384*w-1) := by
  have h0 : inverseAt (3536512*S-63152*w-72) (133504*S-2384*w-1) 0 = some ((884128*S-15788*w-19),(1901760*S-33960*w-37)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (3536512*S-63152*w-72) (133504*S-2384*w-1) 1 = some ((1359568*S-24278*w-28),(950880*S-16980*w-20)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (1901760*S-33960*w-37) ∧ (1901760*S-33960*w-37)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((133504*S-2384*w-1)+(3536512*S-63152*w-72)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (3536512*S-63152*w-72) (133504*S-2384*w-1) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((884128*S-15788*w-19),(1901760*S-33960*w-37)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1359568*S-24278*w-28),(950880*S-16980*w-20)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (3536512*S-63152*w-72) (133504*S-2384*w-1) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((884128*S-15788*w-19),(1901760*S-33960*w-37)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1768256*S-31576*w-42) := by omega
      have hy : c+4 = (1901760*S-33960*w-33) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1359568*S-24278*w-28),(950880*S-16980*w-20)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2719136*S-48556*w-60) := by omega
      have hy : c+4 = (950880*S-16980*w-16) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (2719136*S-48556*w-60) hP (by omega) (by omega)

private theorem block_L1_0_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (688128*S-12288*w-20) (2981888*S-53248*w-37) := by
  have h0 : inverseAt (688128*S-12288*w-20) (2981888*S-53248*w-37) 0 = some ((172032*S-3072*w-6),(3325952*S-59392*w-47)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (688128*S-12288*w-20) (2981888*S-53248*w-37) 1 = some ((1003520*S-17920*w-18),(1662976*S-29696*w-25)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (3325952*S-59392*w-47) ∧ (3325952*S-59392*w-47)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (688128*S-12288*w-20) (2981888*S-53248*w-37) 2 = some ((1419264*S-25344*w-24),(831488*S-14848*w-14)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1662976*S-29696*w-25) ∧ (1662976*S-29696*w-25)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((2981888*S-53248*w-37)+(688128*S-12288*w-20)/2+3)%2^(2+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (688128*S-12288*w-20) (2981888*S-53248*w-37) k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((172032*S-3072*w-6),(3325952*S-59392*w-47)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1003520*S-17920*w-18),(1662976*S-29696*w-25)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1419264*S-25344*w-24),(831488*S-14848*w-14)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (688128*S-12288*w-20) (2981888*S-53248*w-37) k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((172032*S-3072*w-6),(3325952*S-59392*w-47)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (344064*S-6144*w-16) := by omega
      have hy : c+4 = (3325952*S-59392*w-43) := by omega
      rw [hx,hy]
      exact block_L1_0_0_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1003520*S-17920*w-18),(1662976*S-29696*w-25)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2007040*S-35840*w-40) := by omega
      have hy : c+4 = (1662976*S-29696*w-21) := by omega
      rw [hx,hy]
      exact block_L1_0_0_1_ S w hS hP
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1419264*S-25344*w-24),(831488*S-14848*w-14)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2838528*S-50688*w-52) := by omega
      have hy : c+4 = (831488*S-14848*w-10) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (2838528*S-50688*w-52) hP (by omega) (by omega)

private theorem block_L1_1_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (1261568*S-22528*w-28) (2408448*S-43008*w-31) := by
  have h0 : inverseAt (1261568*S-22528*w-28) (2408448*S-43008*w-31) 0 = some ((315392*S-5632*w-8),(3039232*S-54272*w-45)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (1261568*S-22528*w-28) (2408448*S-43008*w-31) 1 = some ((1075200*S-19200*w-19),(1519616*S-27136*w-24)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (3039232*S-54272*w-45) ∧ (3039232*S-54272*w-45)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((2408448*S-43008*w-31)+(1261568*S-22528*w-28)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1261568*S-22528*w-28) (2408448*S-43008*w-31) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((315392*S-5632*w-8),(3039232*S-54272*w-45)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1075200*S-19200*w-19),(1519616*S-27136*w-24)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1261568*S-22528*w-28) (2408448*S-43008*w-31) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((315392*S-5632*w-8),(3039232*S-54272*w-45)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (630784*S-11264*w-20) := by omega
      have hy : c+4 = (3039232*S-54272*w-41) := by omega
      rw [hx,hy]
      exact block_L1_1_0_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1075200*S-19200*w-19),(1519616*S-27136*w-24)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2150400*S-38400*w-42) := by omega
      have hy : c+4 = (1519616*S-27136*w-20) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_1_2_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (3067904*S-54784*w-56) (602112*S-10752*w-7) := by
  have h0 : inverseAt (3067904*S-54784*w-56) (602112*S-10752*w-7) 0 = some ((766976*S-13696*w-15),(2136064*S-38144*w-35)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (3067904*S-54784*w-56) (602112*S-10752*w-7) 1 = some ((1300992*S-23232*w-24),(1068032*S-19072*w-19)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2136064*S-38144*w-35) ∧ (2136064*S-38144*w-35)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (3067904*S-54784*w-56) (602112*S-10752*w-7) 2 = some ((1568000*S-28000*w-29),(534016*S-9536*w-11)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1068032*S-19072*w-19) ∧ (1068032*S-19072*w-19)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h3 : inverseAt (3067904*S-54784*w-56) (602112*S-10752*w-7) 3 = some ((1701504*S-30384*w-32),(267008*S-4768*w-7)) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ (534016*S-9536*w-11) ∧ (534016*S-9536*w-11)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h4 : inverseAt (3067904*S-54784*w-56) (602112*S-10752*w-7) 4 = some ((1768256*S-31576*w-34),(133504*S-2384*w-5)) := by
    rw [inverseAt, h3]
    have hc : 3 ≤ (267008*S-4768*w-7) ∧ (267008*S-4768*w-7)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h5 : inverseAt (3067904*S-54784*w-56) (602112*S-10752*w-7) 5 = some ((1801632*S-32172*w-35),(66752*S-1192*w-4)) := by
    rw [inverseAt, h4]
    have hc : 3 ≤ (133504*S-2384*w-5) ∧ (133504*S-2384*w-5)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((602112*S-10752*w-7)+(3067904*S-54784*w-56)/2+3)%2^(5+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (3067904*S-54784*w-56) (602112*S-10752*w-7) k 1 5 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((766976*S-13696*w-15),(2136064*S-38144*w-35)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1300992*S-23232*w-24),(1068032*S-19072*w-19)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1568000*S-28000*w-29),(534016*S-9536*w-11)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=((1701504*S-30384*w-32),(267008*S-4768*w-7)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h4] at hval
      have hp : (k,1)=((1768256*S-31576*w-34),(133504*S-2384*w-5)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h5] at hval
      have hp : (k,1)=((1801632*S-32172*w-35),(66752*S-1192*w-4)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (3067904*S-54784*w-56) (602112*S-10752*w-7) k c 5 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((766976*S-13696*w-15),(2136064*S-38144*w-35)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1533952*S-27392*w-34) := by omega
      have hy : c+4 = (2136064*S-38144*w-31) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1300992*S-23232*w-24),(1068032*S-19072*w-19)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2601984*S-46464*w-52) := by omega
      have hy : c+4 = (1068032*S-19072*w-15) := by omega
      rw [hx,hy]
      exact block_L1_1_2_1_ S w hS hP
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1568000*S-28000*w-29),(534016*S-9536*w-11)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3136000*S-56000*w-62) := by omega
      have hy : c+4 = (534016*S-9536*w-7) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h3] at hval
      have hp : (k,c)=((1701504*S-30384*w-32),(267008*S-4768*w-7)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3403008*S-60768*w-68) := by omega
      have hy : c+4 = (267008*S-4768*w-3) := by omega
      rw [hx,hy]
      exact block_L1_1_2_3_ S w hS hP
    · subst t
      rw [h4] at hval
      have hp : (k,c)=((1768256*S-31576*w-34),(133504*S-2384*w-5)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3536512*S-63152*w-72) := by omega
      have hy : c+4 = (133504*S-2384*w-1) := by omega
      rw [hx,hy]
      exact block_L1_1_2_4_ S w hS hP
    · subst t
      rw [h5] at hval
      have hp : (k,c)=((1801632*S-32172*w-35),(66752*S-1192*w-4)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3603264*S-64344*w-74) := by omega
      have hy : c+4 = (66752*S-1192*w) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_0_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (1376256*S-24576*w-28) (2293760*S-40960*w-27) := by
  have h0 : inverseAt (1376256*S-24576*w-28) (2293760*S-40960*w-27) 0 = some ((344064*S-6144*w-8),(2981888*S-53248*w-41)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (1376256*S-24576*w-28) (2293760*S-40960*w-27) 1 = some ((1089536*S-19456*w-18),(1490944*S-26624*w-22)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2981888*S-53248*w-41) ∧ (2981888*S-53248*w-41)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((2293760*S-40960*w-27)+(1376256*S-24576*w-28)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1376256*S-24576*w-28) (2293760*S-40960*w-27) k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((344064*S-6144*w-8),(2981888*S-53248*w-41)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1089536*S-19456*w-18),(1490944*S-26624*w-22)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1376256*S-24576*w-28) (2293760*S-40960*w-27) k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((344064*S-6144*w-8),(2981888*S-53248*w-41)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (688128*S-12288*w-20) := by omega
      have hy : c+4 = (2981888*S-53248*w-37) := by omega
      rw [hx,hy]
      exact block_L1_0_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1089536*S-19456*w-18),(1490944*S-26624*w-22)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2179072*S-38912*w-40) := by omega
      have hy : c+4 = (1490944*S-26624*w-18) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (2179072*S-38912*w-40) hP (by omega) (by omega)

private theorem block_L1_1_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (2523136*S-45056*w-44) (1146880*S-20480*w-13) := by
  have h0 : inverseAt (2523136*S-45056*w-44) (1146880*S-20480*w-13) 0 = some ((630784*S-11264*w-12),(2408448*S-43008*w-35)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (2523136*S-45056*w-44) (1146880*S-20480*w-13) 1 = some ((1232896*S-22016*w-21),(1204224*S-21504*w-19)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2408448*S-43008*w-35) ∧ (2408448*S-43008*w-35)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (2523136*S-45056*w-44) (1146880*S-20480*w-13) 2 = some ((1533952*S-27392*w-26),(602112*S-10752*w-11)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1204224*S-21504*w-19) ∧ (1204224*S-21504*w-19)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h3 : inverseAt (2523136*S-45056*w-44) (1146880*S-20480*w-13) 3 = some ((1684480*S-30080*w-29),(301056*S-5376*w-7)) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ (602112*S-10752*w-11) ∧ (602112*S-10752*w-11)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h4 : inverseAt (2523136*S-45056*w-44) (1146880*S-20480*w-13) 4 = some ((1759744*S-31424*w-31),(150528*S-2688*w-5)) := by
    rw [inverseAt, h3]
    have hc : 3 ≤ (301056*S-5376*w-7) ∧ (301056*S-5376*w-7)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h5 : inverseAt (2523136*S-45056*w-44) (1146880*S-20480*w-13) 5 = some ((1797376*S-32096*w-32),(75264*S-1344*w-4)) := by
    rw [inverseAt, h4]
    have hc : 3 ≤ (150528*S-2688*w-5) ∧ (150528*S-2688*w-5)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((1146880*S-20480*w-13)+(2523136*S-45056*w-44)/2+3)%2^(5+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2523136*S-45056*w-44) (1146880*S-20480*w-13) k 1 5 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((630784*S-11264*w-12),(2408448*S-43008*w-35)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1232896*S-22016*w-21),(1204224*S-21504*w-19)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1533952*S-27392*w-26),(602112*S-10752*w-11)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=((1684480*S-30080*w-29),(301056*S-5376*w-7)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h4] at hval
      have hp : (k,1)=((1759744*S-31424*w-31),(150528*S-2688*w-5)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h5] at hval
      have hp : (k,1)=((1797376*S-32096*w-32),(75264*S-1344*w-4)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2523136*S-45056*w-44) (1146880*S-20480*w-13) k c 5 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((630784*S-11264*w-12),(2408448*S-43008*w-35)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1261568*S-22528*w-28) := by omega
      have hy : c+4 = (2408448*S-43008*w-31) := by omega
      rw [hx,hy]
      exact block_L1_1_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1232896*S-22016*w-21),(1204224*S-21504*w-19)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2465792*S-44032*w-46) := by omega
      have hy : c+4 = (1204224*S-21504*w-15) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1533952*S-27392*w-26),(602112*S-10752*w-11)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3067904*S-54784*w-56) := by omega
      have hy : c+4 = (602112*S-10752*w-7) := by omega
      rw [hx,hy]
      exact block_L1_1_2_ S w hS hP
    · subst t
      rw [h3] at hval
      have hp : (k,c)=((1684480*S-30080*w-29),(301056*S-5376*w-7)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3368960*S-60160*w-62) := by omega
      have hy : c+4 = (301056*S-5376*w-3) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h4] at hval
      have hp : (k,c)=((1759744*S-31424*w-31),(150528*S-2688*w-5)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3519488*S-62848*w-66) := by omega
      have hy : c+4 = (150528*S-2688*w-1) := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h5] at hval
      have hp : (k,c)=((1797376*S-32096*w-32),(75264*S-1344*w-4)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3594752*S-64192*w-68) := by omega
      have hy : c+4 = (75264*S-1344*w) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (3594752*S-64192*w-68) hP (by omega) (by omega)

private theorem block_L1_ (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (2752512*S-49152*w-44) (917504*S-16384*w-9) := by
  have h0 : inverseAt (2752512*S-49152*w-44) (917504*S-16384*w-9) 0 = some ((688128*S-12288*w-12),(2293760*S-40960*w-31)) := by
    simp [inverseAt] <;> omega
  have h1 : inverseAt (2752512*S-49152*w-44) (917504*S-16384*w-9) 1 = some ((1261568*S-22528*w-20),(1146880*S-20480*w-17)) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ (2293760*S-40960*w-31) ∧ (2293760*S-40960*w-31)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have h2 : inverseAt (2752512*S-49152*w-44) (917504*S-16384*w-9) 2 = some ((1548288*S-27648*w-24),(573440*S-10240*w-10)) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ (1146880*S-20480*w-17) ∧ (1146880*S-20480*w-17)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq] <;> omega
  have hn : ((917504*S-16384*w-9)+(2752512*S-49152*w-44)/2+3)%2^(2+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2752512*S-49152*w-44) (917504*S-16384*w-9) k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=((688128*S-12288*w-12),(2293760*S-40960*w-31)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=((1261568*S-22528*w-20),(1146880*S-20480*w-17)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=((1548288*S-27648*w-24),(573440*S-10240*w-10)) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2752512*S-49152*w-44) (917504*S-16384*w-9) k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=((688128*S-12288*w-12),(2293760*S-40960*w-31)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (1376256*S-24576*w-28) := by omega
      have hy : c+4 = (2293760*S-40960*w-27) := by omega
      rw [hx,hy]
      exact block_L1_0_ S w hS hP
    · subst t
      rw [h1] at hval
      have hp : (k,c)=((1261568*S-22528*w-20),(1146880*S-20480*w-17)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (2523136*S-45056*w-44) := by omega
      have hy : c+4 = (1146880*S-20480*w-13) := by omega
      rw [hx,hy]
      exact block_L1_1_ S w hS hP
    · subst t
      rw [h2] at hval
      have hp : (k,c)=((1548288*S-27648*w-24),(573440*S-10240*w-10)) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = (3096576*S-55296*w-52) := by omega
      have hy : c+4 = (573440*S-10240*w-6) := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_power_class S w (3096576*S-55296*w-52) hP (by omega) (by omega)

theorem root1_blocked (S w : Nat) (hS:w+1≤S)
    (hP:2^(16*(2048*w+1))=65536*S) :
    Blocked (2752512*S-49152*w-44) (917504*S-16384*w-9) :=
  block_L1_ S w hS hP

#print axioms root0_blocked
#print axioms root1_blocked
end BB6.Agent33Q1Class
