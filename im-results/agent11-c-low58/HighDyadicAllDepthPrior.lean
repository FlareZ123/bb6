import ValSixC58
import HighDyadicDepthFamily
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11C58AllDepthPrior

/-- A reusable exact source-sieve admission rectangle.
    Every j=215 mod256 and m=3 mod256 with an odd authentic stopping
    right coordinate survives the earlier entire ValSixFull+C58 predicate. -/
theorem old_sieve_admits_215_3 (j m : Nat)
    (hj : j%256=215) (hm : m%256=3)
    (hk : (2^(2*m+2)*(j+3)-(j+3*m+5))%2=1) :
    BB6.Agent11C58ValSix.highAllowed j m := by
  have hbase : BB6.Agent3.jointHighAllowed j m := by
    unfold BB6.Agent3.jointHighAllowed
    refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
  have hrect : BB6.Agent3.jointHighRectAllowed j m := by
    unfold BB6.Agent3.jointHighRectAllowed
    exact ⟨hbase,by omega⟩
  have hdy : ∀ n, ¬(n+4≤2*m+2 ∧
      (j+3*m+3)%2^(n+4)=2^(n+2) ∧
      (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    rintro ⟨_,_,hx⟩
    have hx1 : (2*j+3)%8=1 := by omega
    by_cases heven : n%2=0
    · simp [heven] at hx
      omega
    · simp [heven] at hx
      omega
  have h19 : BB6.Agent19Joint.highAllowed j m := by
    unfold BB6.Agent19Joint.highAllowed
    refine ⟨hrect,hdy,?_,?_,?_,?_⟩ <;> omega
  have h29 : BB6.Agent29Joint.highAllowedPlus j m := by
    unfold BB6.Agent29Joint.highAllowedPlus
    exact ⟨h19,by omega,by omega,by omega,by omega⟩
  have hval : BB6.Agent3ValSix.highAllowedValSixThree j m := by
    unfold BB6.Agent3ValSix.highAllowedValSixThree
      BB6.Agent3ValSix.highAllowedValSix
    exact ⟨⟨h29,by omega,by omega⟩,by omega⟩
  have h11 : BB6.Agent11Joint.highAllowed j m := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨h19,by omega,by omega⟩
  have hfive : BB6.Agent19Five.highAllowed j m := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by omega⟩
  let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
  have hguard : ¬(4≤k ∧ k%2=0 ∧ ((2*j+3)+k)%4=1) := by
    dsimp [k]
    omega
  have hnorm : BB6.Agent15.affineNormalize (2*j+3) k=(2*j+3,k) := by
    simp [BB6.Agent15.affineNormalize,hguard]
  have hright : (BB6.Agent15.affineNormalize (2*j+3) k).2 ≠ 4 := by
    rw [hnorm]
    dsimp [k]
    omega
  have hall : BB6.Agent3ValSix.highAllowedValSixFull j m := by
    unfold BB6.Agent3ValSix.highAllowedValSixFull
    refine ⟨hval,hfive,?_,?_,?_,?_⟩
    · omega
    · omega
    · omega
    · simpa [k] using hright
  have hnot58 : ¬(3≤m ∧ j%32=31 ∧ (j+3*m+5)%256=198) := by
    omega
  exact ⟨hall,hnot58⟩

/-- Explicit infinite sequence of depths, each with an original-source
    high stopping target surviving the previous combined high sieve. -/
theorem distinct_depth_family_survives_old (t : Nat) :
    BB6.Agent11C58ValSix.highAllowed
      (BB6.Agent19AllDepth.depthJ (130+128*t))
      (BB6.Agent19AllDepth.depthM (130+128*t)) := by
  let r := 130+128*t
  let j := BB6.Agent19AllDepth.depthJ r
  let m := BB6.Agent19AllDepth.depthM r
  let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
  have hr : 2≤r := by dsimp [r]; omega
  have hmres : m%256=3 := by
    dsimp [m,BB6.Agent19AllDepth.depthM,r]
    omega
  have hsum : j+9*m+14=3*2^(r+2) :=
    BB6.Agent19AllDepth.depth_family_exact_sum r hr
  have hp256 : 256∣(2:Nat)^(r+2) := by
    simpa only [show (2:Nat)^8=256 by decide] using
      (Nat.pow_dvd_pow 2 (by dsimp [r]; omega : 8≤r+2))
  have hprod256 : 256∣3*2^(r+2) := by
    obtain ⟨z,hz⟩ := hp256
    refine ⟨3*z,?_⟩
    rw [hz]
    omega
  have hprod0 : (3*2^(r+2))%256=0 := Nat.mod_eq_zero_of_dvd hprod256
  have hjres : j%256=215 := by omega
  obtain ⟨hm3,hdepth,hm4,hpair⟩ :=
    BB6.Agent19AllDepth.depth_family_parameters r hr
  have hp : 8*m+8≤2^(2*m+2) :=
    BB6.Agent19HighDyadic.eight_power_bound m (by omega)
  have hpos : 1≤2^(2*m+2) := Nat.pow_pos (by decide)
  have hjlow : j≤2^(2*m+2)*j := by
    simpa using Nat.mul_le_mul_right j hpos
  have hmul : 3*(8*m+8)≤3*2^(2*m+2) := by omega
  have hbound : j+3*m+5≤2^(2*m+2)*(j+3) := by
    rw [Nat.mul_add]
    omega
  have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
    dsimp [k]
    have hh := Nat.sub_add_cancel hbound
    omega
  have hkodd : k%2=1 :=
    (BB6.Agent19AllDepth.powered_depth_core
      r j m k hr hm3 hdepth hm4 hpair hstop).1
  exact old_sieve_admits_215_3 j m hjres hmres hkodd

#print axioms old_sieve_admits_215_3
#print axioms distinct_depth_family_survives_old
end BB6.Agent11C58AllDepthPrior
