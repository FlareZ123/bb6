import AffNormFamilyB
import Lean.Elab.Tactic.Omega

namespace BB6.Agent27InfiniteStrictB

/-- For the selected affine family, Agent19's old dyadic high gate
    never fires at any natural exponent. The s-value has valuation 8
    while the odd-parity endpoint requires an odd depth. -/
private theorem odd_forall_raw (t:Nat) :
  ∀ n : Nat, ¬ (n+4≤2*11+2 ∧
      (3292+4096*t+3*11+3)%2^(n+4)=2^(n+2) ∧
      (2*(3292+4096*t)+3)%8=(if n%2=0 then 7 else 3)) := by
  intro n
  rintro ⟨hn,hmod,hdir⟩
  have hleft : (2*(3292+4096*t)+3)%8=3 := by omega
  rw [hleft] at hdir
  have hodd : n%2=1 := by
    by_cases he:n%2=0
    · simp only [he, if_pos] at hdir
      omega
    · omega
  by_cases hs: n≤6
  · have hor : n=1 ∨ n=3 ∨ n=5 := by omega
    rcases hor with rfl | rfl | rfl
    · simp only [show (2:Nat)^(1+4)=32 by decide,
          show (2:Nat)^(1+2)=8 by decide] at hmod
      omega
    · simp only [show (2:Nat)^(3+4)=128 by decide,
          show (2:Nat)^(3+2)=32 by decide] at hmod
      omega
    · simp only [show (2:Nat)^(5+4)=512 by decide,
          show (2:Nat)^(5+2)=128 by decide] at hmod
      omega
  · have hn7:7≤n := by omega
    have hd1 : 512 ∣ (2:Nat)^(n+4) := by
      have hd : (2:Nat)^9 ∣ (2:Nat)^(n+4) := Nat.pow_dvd_pow 2 (by omega)
      simpa using hd
    have hd2 : 512 ∣ (2:Nat)^(n+2) := by
      have hd : (2:Nat)^9 ∣ (2:Nat)^(n+2) := Nat.pow_dvd_pow 2 (by omega)
      simpa using hd
    have hc := congrArg (fun x:Nat => x%512) hmod
    rw [Nat.mod_mod_of_dvd _ hd1, Nat.mod_eq_zero_of_dvd hd2] at hc
    omega

/-- The independently integrated Agent11 all-depth sieve never fires
    on this family: the source value j+9m+14 is odd. -/
private theorem older_c58_forall_raw (t:Nat) :
  ∀ r : Nat, ¬(2≤r ∧ 3≤11 ∧ r+4≤2*11+2 ∧
      11%4=(2*r+3)%4 ∧
      (3292+4096*t+9*11+14)%2^(r+4)=3*2^(r+2)) := by
  intro r
  rintro ⟨hr,_,_,_,hmod⟩
  have hd1 : 16 ∣ (2:Nat)^(r+4) := by
    have h : (2:Nat)^4 ∣ (2:Nat)^(r+4) := Nat.pow_dvd_pow 2 (by omega)
    simpa using h
  have hd2 : 16 ∣ 3*(2:Nat)^(r+2) := by
    have h : (2:Nat)^4 ∣ (2:Nat)^(r+2) := Nat.pow_dvd_pow 2 (by omega)
    have h' : 16 ∣ (2:Nat)^(r+2) := by simpa using h
    rcases h' with ⟨q,hq⟩
    refine ⟨3*q,?_⟩
    rw [hq]
    ac_rfl
  have hc := congrArg (fun x:Nat => x%16) hmod
  rw [Nat.mod_mod_of_dvd _ hd1, Nat.mod_eq_zero_of_dvd hd2] at hc
  omega

def highIndex (t:Nat) : Nat := 3292+4096*t

private theorem odd_forall (t:Nat) :
  ∀ n : Nat, ¬(n+4≤2*11+2 ∧
       (highIndex t+3*11+3)%2^(n+4)=2^(n+2) ∧
       (2*highIndex t+3)%8=(if n%2=0 then 7 else 3)) := by
  simpa only [highIndex] using odd_forall_raw t

private theorem older_c58_forall (t:Nat) :
  ∀ r : Nat, ¬(2≤r ∧ 3≤11 ∧ r+4≤2*11+2 ∧
    11%4=(2*r+3)%4 ∧
    (highIndex t+9*11+14)%2^(r+4)=3*2^(r+2)) := by
  simpa only [highIndex] using older_c58_forall_raw t

private theorem high_normalizer (t:Nat) :
  (BB6.Agent15.affineNormalize
     (2*highIndex t+3)
     (2^(2*11+2)*(highIndex t+3)-(highIndex t+3*11+5))).2 =
       BB6.Agent27NormB.k7 t := by
  have ha : 2*highIndex t+3 = BB6.Agent27NormB.a0 t := by
    dsimp [highIndex,BB6.Agent27NormB.a0]
    omega
  have hk : 2^(2*11+2)*(highIndex t+3)-(highIndex t+3*11+5) =
       BB6.Agent27NormB.k0 t := by
    have hp : (2:Nat)^(2*11+2)=16777216 := by decide
    rw [hp]
    dsimp [highIndex,BB6.Agent27NormB.k0]
    omega
  rw [ha,hk,BB6.Agent27NormB.norm_family]

private theorem high_normalizer_not_four (t:Nat) :
  (BB6.Agent15.affineNormalize
     (2*highIndex t+3)
     (2^(2*11+2)*(highIndex t+3)-(highIndex t+3*11+5))).2 ≠ 4 := by
  rw [high_normalizer]
  dsimp [BB6.Agent27NormB.k7]
  omega

/-- Every member of this infinite family passes the *entire* prior
    integrated source high sieve, including the affine normalizer,
    historical odd-depth and C58 all-depth constraints. -/
theorem prior_source_admits_all (t:Nat) :
    BB6.Agent11C58AllDepth.highAllowed (highIndex t) 11 := by
  have h3 : BB6.Agent3.jointHighAllowed (highIndex t) 11 := by
    unfold BB6.Agent3.jointHighAllowed
    dsimp [highIndex]
    omega
  have hrect : BB6.Agent3.jointHighRectAllowed (highIndex t) 11 := by
    unfold BB6.Agent3.jointHighRectAllowed
    exact ⟨h3,by dsimp [highIndex]; omega⟩
  have h19 : BB6.Agent19Joint.highAllowed (highIndex t) 11 := by
    unfold BB6.Agent19Joint.highAllowed
    refine ⟨hrect,odd_forall t,?_⟩
    dsimp [highIndex]
    omega
  have h29 : BB6.Agent29Joint.highAllowedPlus (highIndex t) 11 := by
    unfold BB6.Agent29Joint.highAllowedPlus
    refine ⟨h19,?_⟩
    dsimp [highIndex]
    omega
  have hval : BB6.Agent3ValSix.highAllowedValSixThree (highIndex t) 11 := by
    unfold BB6.Agent3ValSix.highAllowedValSixThree
      BB6.Agent3ValSix.highAllowedValSix
    refine ⟨⟨h29,?_⟩,?_⟩ <;> dsimp [highIndex] <;> omega
  have h11 : BB6.Agent11Joint.highAllowed (highIndex t) 11 := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨h19,
      by dsimp [highIndex]; omega,
      by dsimp [highIndex]; omega⟩
  have hfive : BB6.Agent19Five.highAllowed (highIndex t) 11 := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by dsimp [highIndex]; omega⟩
  have hfull : BB6.Agent3ValSix.highAllowedValSixFull (highIndex t) 11 := by
    unfold BB6.Agent3ValSix.highAllowedValSixFull
    exact ⟨hval,hfive,
      by dsimp [highIndex]; omega,
      by dsimp [highIndex]; omega,
      by dsimp [highIndex]; omega,
      high_normalizer_not_four t⟩
  have hc58 : BB6.Agent11C58ValSix.highAllowed (highIndex t) 11 := by
    unfold BB6.Agent11C58ValSix.highAllowed
    exact ⟨hfull,by dsimp [highIndex]; omega⟩
  unfold BB6.Agent11C58AllDepth.highAllowed
  exact ⟨hc58,older_c58_forall t⟩

/-- The exact latest source phase exclusion holds for every member,
    at depth r=8, second branch. -/
theorem phase_excludes_all (t:Nat) :
    BB6.Agent46.allPhaseExcluded (highIndex t) 11 := by
  refine ⟨8,by omega,by omega,Or.inr ⟨?_,?_⟩⟩
  · dsimp [highIndex]
    omega
  · have hp : (2:Nat)^(8+4)=4096 := by decide
    have h8 : (2:Nat)^8=256 := by decide
    rw [hp,h8]
    dsimp [highIndex]
    omega

/-- A source-authentic infinite nonredundancy certificate for the
    new phase sieve, strictly separating it from all integrated older
    high filters. This remains a parameter-space statement. -/
theorem strict_infinite_family (t:Nat) :
    BB6.Agent11C58AllDepth.highAllowed (highIndex t) 11 ∧
    ¬BB6.Agent24Phase.highAllowed (highIndex t) 11 := by
  refine ⟨prior_source_admits_all t,?_⟩
  intro h
  exact h.2 (phase_excludes_all t)

/-- Distinct t give strictly increasing and therefore distinct j. -/
theorem highIndex_strict (t:Nat) : highIndex t < highIndex (t+1) := by
  dsimp [highIndex]
  omega

#print axioms prior_source_admits_all
#print axioms phase_excludes_all
#print axioms strict_infinite_family
end BB6.Agent27InfiniteStrictB
