import Lean.Elab.Tactic.Omega
namespace BB6.Agent30Generic

def H (r c s z : Nat) : Nat := r*(z/2)+c+s*(z%2)
def iterH (r c s : Nat) : Nat → Nat → Nat
  | 0,z => z
  | n+1,z => iterH r c s n (H r c s z)

theorem H_even_shift (r c s z d : Nat) :
    H r c s (z+2*d)=H r c s z+r*d := by
  have hd : (z+2*d)/2=z/2+d := by omega
  have hp : (z+2*d)%2=z%2 := by omega
  simp only [H, hd, hp]
  simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem iterH_two_adic_shift (r c s n z d : Nat) :
    iterH r c s n (z+2^n*d)=iterH r c s n z+r^n*d := by
  induction n generalizing z d with
  | zero => simp [iterH]
  | succ n ih =>
    change iterH r c s n (H r c s (z+2^(n+1)*d)) =
      iterH r c s n (H r c s z) + r^(n+1)*d
    have hpow : 2^(n+1)*d = 2*(2^n*d) := by
      rw [Nat.pow_succ]
      ac_rfl
    rw [hpow,H_even_shift]
    have hin : H r c s z + r*(2^n*d) = H r c s z + 2^n*(r*d) := by
      ac_rfl
    rw [hin,ih]
    rw [Nat.pow_succ]
    ac_rfl

theorem H_odd_scale_curvature (r c s y t : Nat)
    (hr : r%2=1) (hs:t%2=1) (hgap:r≤2*s) :
    (y%2=0 ∧ H r c s y+H r c s (y+2*t)+(2*s-r) =
      2*H r c s (y+t)) ∨
    (y%2=1 ∧ H r c s y+H r c s (y+2*t) =
      2*H r c s (y+t)+(2*s-r)) := by
  have ht : t=2*(t/2)+1 := by omega
  have hdelta : r+(2*s-r)=2*s := by omega
  have hrt : r*t=2*(r*(t/2))+r := by
    calc
      r*t = r*(2*(t/2)+1) := congrArg (fun u:Nat=>r*u) ht
      _ = 2*(r*(t/2))+r := by
        rw [Nat.mul_add]
        simp
        ac_rfl
  by_cases hy : y%2=0
  · left
    refine ⟨hy, ?_⟩
    have hmidDiv : (y+t)/2=y/2+t/2 := by omega
    have hmidRem : (y+t)%2=1 := by omega
    have hendDiv : (y+2*t)/2=y/2+t := by omega
    have hendRem : (y+2*t)%2=0 := by omega
    simp only [H,hy,hmidDiv,hmidRem,hendDiv,hendRem]
    rw [Nat.mul_add r (y/2) t,hrt]
    simp [Nat.mul_add]
    omega
  · right
    have hodd : y%2=1 := by omega
    refine ⟨hodd, ?_⟩
    have hmidDiv : (y+t)/2=y/2+t/2+1 := by omega
    have hmidRem : (y+t)%2=0 := by omega
    have hendDiv : (y+2*t)/2=y/2+t := by omega
    have hendRem : (y+2*t)%2=1 := by omega
    simp only [H,hodd,hmidDiv,hmidRem,hendDiv,hendRem]
    rw [Nat.mul_add r (y/2) t,hrt]
    simp [Nat.mul_add]
    omega

theorem iterH_succ_last (r c s n z : Nat) :
    iterH r c s (n+1) z = H r c s (iterH r c s n z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    change iterH r c s (n+1) (H r c s z) =
      H r c s (iterH r c s (n+1) z)
    exact ih (H r c s z)

end BB6.Agent30Generic
