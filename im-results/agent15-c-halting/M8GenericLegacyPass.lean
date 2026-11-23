import M8GenericHigh
import JointAllRoot
import Lean.Elab.Tactic.Omega
namespace BB6.Agent15Research
open BB6.Agent29Depth

/-- At depths beyond the stopping exponent the M8 quotient residue forces
    full divisibility of the old high-parameter dyadic test index. -/
theorem generic_high_index_multiple (m d t j : Nat)
    (hd : 2*m+2≤d)
    (heq : allOddQ m*(j+3)=m+2^d*(2+8*t)) :
    allOddB m ∣ j+3*m+3 := by
  obtain ⟨e,he⟩ : ∃e,d=2*m+2+e :=
    ⟨d-(2*m+2),by omega⟩
  have hpow : 2^d=allOddB m*2^e := by
    rw [he,Nat.pow_add]
    rfl
  have hdvd : allOddB m ∣ 3*2^d*(2+8*t) := by
    refine ⟨3*2^e*(2+8*t),?_⟩
    rw [hpow]
    ac_rfl
  have hB := allOdd_BQ m
  have hwhole : allOddB m*(j+3)=
      (j+3*m+3)+(3*2^d*(2+8*t)) := by
    rw [hB]
    have hmul : 3*allOddQ m*(j+3)=
        3*m+3*2^d*(2+8*t) := by
      calc
        3*allOddQ m*(j+3)=3*(allOddQ m*(j+3)) := by ac_rfl
        _=3*(m+2^d*(2+8*t)) := by rw [heq]
        _=3*m+3*2^d*(2+8*t) := by rw [Nat.mul_add]; ac_rfl
    simp only [Nat.add_mul,Nat.one_mul]
    omega
  have hwhd : allOddB m ∣ allOddB m*(j+3) :=
    ⟨j+3,by ac_rfl⟩
  have hsub := Nat.dvd_sub hwhd hdvd
  have hdiff : (allOddB m*(j+3))-(3*2^d*(2+8*t))=j+3*m+3 := by
    omega
  simpa [hdiff] using hsub

/-- The entire previously maintained Agent19 high-parameter sieve accepts
    every sufficiently deep member of the generic M8 forbidden cylinder. -/
theorem generic_deep_passes_all_legacy_high_sieves (m d t j : Nat)
    (hm : m%2=1)
    (hd : 2*m+2≤d)
    (hdpar : 2*d%4=(m+1)%4)
    (heq : allOddQ m*(j+3)=m+2^d*(2+8*t)) :
    BB6.Agent19Joint.highAllowed j m := by
  have hQ4 : allOddQ m%4=1 := by
    simpa [allOddQ] using m8Geom4_mod_four (m+1) (by omega)
  have heven : 2^d*(2+8*t)%4=0 := by
    obtain ⟨e,he⟩ : ∃e,d=1+e := ⟨d-1,by omega⟩
    have hpow : 2^d=2*2^e := by
      rw [he,Nat.pow_add]
    have hdiv : 4 ∣ 2^d*(2+8*t) := by
      refine ⟨2^e*(1+4*t),?_⟩
      rw [hpow]
      have htwo : 2+8*t=2*(1+4*t) := by omega
      rw [htwo,show (4:Nat)=2*2 by decide]
      ac_rfl
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hjm : (j+3)%4=m%4 := by
    have h := congrArg (fun z : Nat => z%4) heq
    rw [Nat.mul_mod,hQ4] at h
    simp only [Nat.one_mul,Nat.mod_mod,Nat.add_mod,heven] at h
    omega
  have hj2 : j%2=0 := by omega
  have hs : (j+m)%4=3 := by omega
  have hbase : BB6.Agent3.jointHighAllowed j m := by
    dsimp [BB6.Agent3.jointHighAllowed]
    omega
  have hrect : BB6.Agent3.jointHighRectAllowed j m := by
    dsimp [BB6.Agent3.jointHighRectAllowed]
    exact ⟨hbase,by omega⟩
  have hdiv := generic_high_index_multiple m d t j hd heq
  have hz : ∀ n, n+4≤2*m+2 → (j+3*m+3)%2^(n+4)=0 := by
    intro n hn
    have hpowdiv : 2^(n+4) ∣ allOddB m := by
      obtain ⟨e,he⟩ : ∃e,2*m+2=n+4+e :=
        ⟨2*m+2-(n+4),by omega⟩
      refine ⟨2^e,?_⟩
      dsimp [allOddB]
      rw [he,Nat.pow_add]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hpowdiv hdiv)
  change BB6.Agent3.jointHighRectAllowed j m ∧
    (∀ n, ¬(n+4≤2*m+2 ∧
      (j+3*m+3)%2^(n+4)=2^(n+2) ∧
      (2*j+3)%8=(if n%2=0 then 7 else 3))) ∧
    ¬ (2≤m ∧ j%8=7 ∧ (j+3*m+15)%64=0) ∧
    ¬ (2≤m ∧ j%8=3 ∧ (j+3*m+47)%64=0) ∧
    ¬ (3≤m ∧ j%8=5 ∧ (j+3*m+27)%128=0) ∧
    ¬ (3≤m ∧ j%8=1 ∧ (j+3*m+91)%128=0)
  refine ⟨hrect, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rintro ⟨hn,hval,_⟩
    have hzero := hz n hn
    have hpos : 0<2^(n+2) := Nat.pow_pos (by decide)
    omega
  all_goals omega

/-- The new high-depth M8 class is excluded by the source quotient proof,
    although each such index passes every previous Agent19 restriction. -/
theorem generic_deep_new_exclusion (m d t j : Nat)
    (hm : m%2=1)
    (hd : 2*m+2≤d)
    (hdpar : 2*d%4=(m+1)%4)
    (heq : allOddQ m*(j+3)=m+2^d*(2+8*t)) :
    BB6.Agent19Joint.highAllowed j m ∧
    ¬ BB6.Agent15.CReach (2*j+3) (3*2^d*(2+8*t)-2) := by
  exact ⟨generic_deep_passes_all_legacy_high_sieves m d t j hm hd hdpar heq,
    high_m8_diophantine_exclusion m d t j hm (by omega) hdpar heq⟩

#print axioms generic_high_index_multiple
#print axioms generic_deep_passes_all_legacy_high_sieves
#print axioms generic_deep_new_exclusion
end BB6.Agent15Research
