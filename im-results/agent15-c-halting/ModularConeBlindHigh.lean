import ModularConeBlind
import ModularConeHighStop
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent15Research
open BB6.Agent42ModularCone

/-- A generic blind high-stop cylinder. If the original high index j is
    positive and even, m is odd, and the full stopping modulus divides
    j+3m+3, then the adaptive modular-cone checker cannot exclude it. -/
theorem high_stop_blind_of_even_divisible
    (j m : Nat) (hjpos : 1≤j) (hjeven : j%2=0) (hm : m%2=1)
    (hdiv : 2^(2*m+2) ∣ j+3*m+3) :
    highStopExcluded (j+1) m = false := by
  let b := min 32 (2*m+2)
  have hJ : 2≤j+1 := by omega
  have hbits : highStopBits (j+1) m=b := by
    simp [highStopBits,hJ,b]
  have hfull : b≤2*m+2 := Nat.min_le_right _ _
  have hb : 2≤b := by
    have hm1 : 1≤m := by omega
    have h4 : 4≤2*m+2 := by omega
    dsimp [b]
    omega
  have hpow : 2^b ∣ 2^(2*m+2) := by
    obtain ⟨q,hq⟩ : ∃q,2*m+2=b+q := ⟨2*m+2-b,by omega⟩
    refine ⟨2^q,?_⟩
    rw [hq,Nat.pow_add]
  have hsmall : 2^b ∣ j+3*m+3 := Nat.dvd_trans hpow hdiv
  have hposCong : Cong b (((j+3*m+3:Nat):Int)) 0 := by
    rcases hsmall with ⟨q,hq⟩
    unfold Cong I P
    refine ⟨(q:Int),?_⟩
    have hh := congrArg (fun z : Nat => (z:Int)) hq
    simp at hh ⊢
    exact hh
  have hneg := cong_mul_const hposCong (-1)
  have hyCong : Cong b
      (-(((j+1:Nat):Int)+3*(m:Int)+4)) (-2) := by
    have hh := cong_add hneg (cong_refl b (-2))
    have hleft : (-1)*((j+3*m+3:Nat):Int)+(-2) =
        -(((j+1:Nat):Int)+3*(m:Int)+4) := by
      simp
      omega
    rw [hleft] at hh
    exact hh
  have hIge := I_ge4 b hb
  have hminus : Cong b (-2) (I b-2) := by
    unfold Cong
    refine ⟨(-1:Int),?_⟩
    omega
  have hyAll : Cong b (-(((j+1:Nat):Int)+3*(m:Int)+4)) (I b-2) := by
    unfold Cong at hyCong hminus ⊢
    have heq :
        -(((j+1:Nat):Int)+3*(m:Int)+4) - (I b-2) =
          (-(((j+1:Nat):Int)+3*(m:Int)+4) - (-2)) + ((-2) - (I b-2)) := by omega
    rw [heq]
    exact Int.dvd_add hyCong hminus
  have hyMod := cong_mod hyAll
  have hyRange : (I b-2)%I b=I b-2 := Int.emod_eq_of_lt (by omega) (by omega)
  rw [hyRange] at hyMod
  have h4dvd := four_dvd_I b hb
  have hx4 :
      ((2*((j+1:Nat):Int)+1) % I b) % 4 = 3 := by
    rw [Int.emod_emod_of_dvd _ h4dvd]
    omega
  have hblind : Blind b (residue b (stopResidue (j+1) m)) := by
    constructor
    · change ((2*((j+1:Nat):Int)+1)%I b)%4=3
      exact hx4
    · change (-(((j+1:Nat):Int)+3*(m:Int)+4))%I b=I b-2
      exact hyMod
  rw [highStopExcluded,hbits]
  exact blind_excluded_false b (stopResidue (j+1) m) hb hblind

#print axioms high_stop_blind_of_even_divisible
end BB6.Agent15Research
