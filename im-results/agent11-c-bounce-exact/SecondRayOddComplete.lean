import SecondRayShapeOriginal
import SecondRayPowerOdd
import SecondGateFanOriginal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Ray
open BB6.Agent46

/-- Match the Diophantine-normalized high predecessor to the previously
    source-verified explicit family of incoming edges. -/
theorem fan_from_normalized (m s t a k : Nat)
    (hm:m=s+t+1)
    (ha:a+3=4^(t+1)*(3*m+4))
    (hk:k+(2*4^t*(3*m+4)+3*m+7+3*s)=rayD m) :
    a=FanArithmetic.p s t ∧ k=FanArithmetic.q s t := by
  have hB : FanArithmetic.b s t=3*m+4 := by
    dsimp [FanArithmetic.b,FanArithmetic.m]
    omega
  have hA : FanArithmetic.a s t=4^t*(3*m+4) := by
    simp only [FanArithmetic.a,hB]
  have hD : FanArithmetic.d s t=rayD m := by
    dsimp [FanArithmetic.d,rayD]
    rw [hB]
    have hsm : FanArithmetic.m s t=m := by
      dsimp [FanArithmetic.m]
      omega
    rw [hsm]
  have hb := FanArithmetic.bounds s t
  have hp : FanArithmetic.p s t+3=4*FanArithmetic.a s t := by
    have hpbound : 2≤FanArithmetic.p s t := hb.2.2.2.2
    unfold FanArithmetic.p at hpbound ⊢
    omega
  have hpp : FanArithmetic.p s t+3=4^(t+1)*(3*m+4) := by
    rw [hp,hA,Nat.pow_succ]
    ac_rfl
  have hq : FanArithmetic.q s t +
    (2*FanArithmetic.a s t+3*FanArithmetic.m s t+7+3*s)=
    FanArithmetic.d s t := by
    unfold FanArithmetic.q
    exact Nat.sub_add_cancel hb.2.1
  have hqq : FanArithmetic.q s t +
    (2*4^t*(3*m+4)+3*m+7+3*s)=rayD m := by
    rw [hA,hD] at hq
    have hmm : FanArithmetic.m s t=m := by
      dsimp [FanArithmetic.m]
      omega
    rw [hmm] at hq
    calc
      FanArithmetic.q s t + (2*4^t*(3*m+4)+3*m+7+3*s) =
        FanArithmetic.q s t + (2*(4^t*(3*m+4))+3*m+7+3*s) := by congr 1; ac_rfl
      _ = rayD m := hq
  constructor <;> omega

/-- Odd m: the entire exact predecessor fibre is an explicitly finite
    direct predecessor plus the indexed high fan. The power-of-two
    exceptional input is IMPOSSIBLE in this parity class. -/
theorem original_odd_ray_fibre_iff (m a k : Nat) (hm:m%2=1) :
    secNext (a,k)=some (rayX m,rayY m) ↔
    (a+3=rayD m ∧ 2*k+2=rayY m) ∨
    (∃ s t : Nat, m=s+t+1 ∧
       a=FanArithmetic.p s t ∧ k=FanArithmetic.q s t) := by
  constructor
  · intro h
    have hi := (original_ray_parent_iff m a k).mp h
    rcases hi with hd | he | hh
    · exact Or.inl hd
    · obtain ⟨_,_,n,hn,_⟩ := he
      have hpow : rayD m=2^(n+4) := by
        calc
          rayD m=2^n*16 := hn
          _ = 2^(n+4) := by
            rw [Nat.pow_add]
      exact False.elim ((odd_ray_D_not_pow_two m (n+4) hm) hpow)
    · obtain ⟨ha,hlt,n,hn,hpow,hcost⟩ := hh
      have hodd := ray_source_odd m a k
        ((complete_section_inverse a k (rayX m) (rayY m) (by have h:=rayFacts m;omega)).mp h)
      have hnorm := odd_high_parent_normalized m a k hm hodd
        ⟨n,hn,hpow,hcost⟩
      obtain ⟨s,t,hst,hs,ht⟩ := hnorm
      obtain ⟨ha',hk'⟩ := fan_from_normalized m s t a k hst hs ht
      exact Or.inr ⟨s,t,hst,ha',hk'⟩
  · rintro (hd | ⟨s,t,hst,ha,hk⟩)
    · exact (original_ray_parent_iff m a k).mpr (Or.inl hd)
    · have hedge:=BB6.Agent11Research.second_gate_incoming_edge s t
      have htarget : secNext (FanArithmetic.p s t,FanArithmetic.q s t)=
          some (rayX m,rayY m) := by
        have hsm : FanArithmetic.m s t=m := by
          dsimp [FanArithmetic.m]
          omega
        simpa only [rayX,rayY,rayD,hsm] using hedge
      simpa only [ha,hk] using htarget

#print axioms fan_from_normalized
#print axioms original_odd_ray_fibre_iff
end BB6.Agent11Ray
