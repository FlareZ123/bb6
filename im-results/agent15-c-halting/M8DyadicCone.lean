import M8M16Composition
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15

private theorem pow8_factor (t : Nat) :
    2^(t+3) = 8 * 2^t := by
  rw [show t+3=3+t by omega, Nat.pow_add]

private theorem pow8_lower (t : Nat) : 8 ≤ 2^(t+3) := by
  induction t with
  | zero => decide
  | succ t ih =>
      rw [show (t+1)+3=(t+3)+1 by omega, Nat.pow_succ]
      omega

/-- The M8 forbidden inverse cylinder extends through arbitrary 2-adic
affine inverse depth. The left counter alternates modulo eight with depth;
the odd multiplier q remains arbitrary subject to q=3 modulo four.
The conclusion is genuine blank-origin CReach exclusion, conditional on
the original-source M8 bridge. -/
theorem blank_no_m8_dyadic_cone (t q a : Nat) (hq : q%4=3)
    (ha : a%8 = if t%2=0 then 7 else 3) :
    ¬CReach a (2^(t+2)*q-2) := by
  induction t generalizing a with
  | zero =>
      intro hreach
      have haVal : a%8=7 := by simpa using ha
      have ha8 : a=8*(a/8)+7 := by omega
      have hqVal : q=4*(q/4)+3 := by omega
      have hk : 2^(0+2)*q-2=16*(q/4)+10 := by omega
      rw [ha8,hk] at hreach
      exact blank_no_m8_affine_cylinder (a/8) (q/4) hreach
  | succ t ih =>
      intro hreach
      let k := 2^((t+1)+2)*q-2
      have hqbound : 3≤q := by omega
      have hp : 8≤2^((t+1)+2) := by
        simpa [show (t+1)+2=t+3 by omega] using pow8_lower t
      have hmult : 8*q≤2^((t+1)+2)*q := Nat.mul_le_mul_right q hp
      have hkbig : 4≤k := by dsimp [k]; omega
      have hpow8 : 2^((t+1)+2) = 8*2^t := by
        simpa [show (t+1)+2=t+3 by omega] using pow8_factor t
      have hkform : k=8*(2^t*q)-2 := by
        dsimp [k]
        rw [hpow8]
        simp [Nat.mul_assoc]
      have hkmod : k%8=6 := by
        rw [hkform]
        omega
      have heven : k%2=0 := by omega
      have haMod4 : a%4=3 := by
        by_cases he : t%2=0
        · have hpar : (t+1)%2=1 := by omega
          have haa : a%8=3 := by simpa [hpar] using ha
          omega
        · have hpar : (t+1)%2=0 := by omega
          have haa : a%8=7 := by simpa [hpar] using ha
          omega
      have hsum : (a+k)%4=1 := by omega
      have hpow2 : 2^((t+1)+2)=2*2^(t+2) := by
        rw [show (t+1)+2=(t+2)+1 by omega,Nat.pow_succ]
        omega
      have hkpred : (k-2)/2=2^(t+2)*q-2 := by
        dsimp [k]
        rw [hpow2]
        rw [show 2*2^(t+2)*q = 2*(2^(t+2)*q) by ac_rfl]
        omega
      have haPred : (a+k-2)%8 = if t%2=0 then 7 else 3 := by
        by_cases he : t%2=0
        · have hpar : (t+1)%2=1 := by omega
          have haa : a%8=3 := by simpa [hpar] using ha
          simp [he]
          omega
        · have hpar : (t+1)%2=0 := by omega
          have haa : a%8=7 := by simpa [hpar] using ha
          simp [he]
          omega
      have hpre := (blank_reach_iff_affine a k hkbig heven hsum).mp hreach
      rw [hkpred] at hpre
      exact ih (a+k-2) haPred hpre

#print axioms blank_no_m8_dyadic_cone
end BB6.Agent15
