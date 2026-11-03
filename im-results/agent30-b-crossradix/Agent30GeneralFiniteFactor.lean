import Agent30CrossRadix

namespace BB6.Agent30GeneralFactor
open BB6.Agent30Cross (nat_add_mod_cancel)

def H (r c s z : Nat) : Nat := r*(z/2)+c+s*(z%2)
def iterH (r c s : Nat) : Nat → Nat → Nat
  | 0,z => z
  | n+1,z => H r c s (iterH r c s n z)

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
    change H r c s (iterH r c s n (z+2^(n+1)*d)) =
      H r c s (iterH r c s n z)+r^(n+1)*d
    have hp : 2^(n+1)*d=2^n*(2*d) := by simp[Nat.pow_succ];ac_rfl
    rw [hp, ih]
    have hmul : r^n*(2*d)=2*(r^n*d) := by ac_rfl
    rw [hmul,H_even_shift]
    simp only [Nat.pow_succ]
    ac_rfl

theorem H_double (r c s z : Nat) (hgap : r≤2*s) :
    2*H r c s z = r*z+2*c+(2*s-r)*(z%2) := by
  have hdelta : r+(2*s-r)=2*s := by omega
  rcases Nat.mod_two_eq_zero_or_one z with hp | hp
  · have hz : r*z=2*(r*(z/2)) := by
      have hzz : z=2*(z/2) := by omega
      calc
        r*z = r*(2*(z/2)) := congrArg (fun w:Nat => r*w) hzz
        _ = 2*(r*(z/2)) := by ac_rfl
    simp only [H, hp, Nat.mul_zero, Nat.add_zero]
    omega
  · have hz : r*z=2*(r*(z/2))+r := by
      have hzz : z=2*(z/2)+1 := by omega
      calc
        r*z = r*(2*(z/2)+1) := congrArg (fun w:Nat => r*w) hzz
        _ = 2*(r*(z/2))+r := by simp [Nat.mul_add]; ac_rfl
    simp only [H, hp, Nat.mul_one]
    omega

private theorem mul_mod_lift (a b m : Nat) (h : a%m=b%m) :
    (2*a)%m = (2*b)%m := by
  calc
    (2*a)%m = (2*(a%m))%m := by simp [Nat.mul_mod]
    _ = (2*(b%m))%m := by rw [h]
    _ = (2*b)%m := by simp [Nat.mul_mod]

private theorem H_shift_bal (r c s z d : Nat) (hgap:r≤2*s) :
    2*(H r c s (z+d))+(2*s-r)*(z%2) =
      2*(H r c s z)+r*d+(2*s-r)*((z+d)%2) := by
  have ha:=H_double r c s z hgap
  have hb:=H_double r c s (z+d) hgap
  have hrdistrib : r*(z+d)=r*z+r*d := by rw [Nat.mul_add]
  omega

theorem H_odd_multiplier_obstruction (r c s z m q : Nat)
    (hr : r%2=1) (hgap : r≤2*s)
    (hm : 0<m) (hq : q%2=1)
    (h : (H r c s (z+m*q))%m = (H r c s z)%m) : m ∣ (2*s-r) := by
  by_cases hme : m%2=0
  · let t := m/2
    have hm2 : m=2*t := by dsimp [t]; omega
    have hs : 0<t := by omega
    have hshift : m*q = 2*(t*q) := by rw [hm2]; ac_rfl
    rw [hshift, H_even_shift r c s] at h
    have hzero : (r*t*q)%(2*t) = 0 := by
      have hh : (r*t*q + H r c s z)%(2*t) = (0 + H r c s z)%(2*t) := by
        simpa [Nat.add_comm, Nat.mul_assoc, hm2] using h
      exact (nat_add_mod_cancel (r*t*q) 0 (H r c s z) (2*t)).mp hh
    have hodd : (r*q)%2=1 := by rw [Nat.mul_mod, hr, hq]
    have hrem : (r*t*q)%(2*t)=t := by
      have hh: r*t*q=t*(r*q) := by ac_rfl
      rw [hh, show 2*t = t*2 by omega, Nat.mul_mod_mul_left, hodd]
      simp
    omega
  · have hmo : m%2=1 := by omega
    have hdodd : (m*q)%2=1 := by rw [Nat.mul_mod, hmo, hq]
    have hpz : z%2<2 := Nat.mod_lt _ (by decide)
    have hpzd : (z+m*q)%2<2 := Nat.mod_lt _ (by decide)
    have hdpar : z%2+(z+m*q)%2=1 := by omega
    have h2 := mul_mod_lift ((H r c s (z+m*q))) (H r c s z) m h
    have hbal := H_shift_bal r c s z (m*q) hgap
    have hrd : (r*(m*q))%m=0 := by simp [Nat.mul_mod, Nat.mul_assoc]
    have hb : (2*s-r)%m = 0 := by
      rcases Nat.mod_two_eq_zero_or_one z with hp | hp
      · have hp' : (z+m*q)%2=1 := by omega
        rw [hp,hp'] at hbal
        simp only [Nat.mul_zero,Nat.mul_one,Nat.add_zero] at hbal
        have hred : ((2*(H r c s z))+(2*s-r))%m = (2*(H r c s z))%m := by
          calc
            ((2*(H r c s z))+(2*s-r))%m = (2*(H r c s z)+r*(m*q)+(2*s-r))%m := by
              simp [Nat.add_mod,hrd,Nat.add_assoc]
            _ = (2*(H r c s (z+m*q)))%m := by rw [←hbal]
            _ = (2*(H r c s z))%m := h2
        exact (nat_add_mod_cancel (2*s-r) 0 (2*(H r c s z)) m).mp (by simpa [Nat.add_comm] using hred)
      · have hp' : (z+m*q)%2=0 := by omega
        rw [hp,hp'] at hbal
        simp only [Nat.mul_zero,Nat.mul_one,Nat.add_zero] at hbal
        have hred : ((2*(H r c s (z+m*q)))+(2*s-r))%m = (2*(H r c s (z+m*q)))%m := by
          calc
            ((2*(H r c s (z+m*q)))+(2*s-r))%m = (2*(H r c s z)+r*(m*q))%m := by rw [hbal]
            _ = (2*(H r c s z))%m := by simp [Nat.add_mod,hrd]
            _ = (2*(H r c s (z+m*q)))%m := h2.symm
        exact (nat_add_mod_cancel (2*s-r) 0 (2*(H r c s (z+m*q))) m).mp (by simpa [Nat.add_comm] using hred)
    exact Nat.dvd_of_mod_eq_zero hb

#print axioms H_odd_multiplier_obstruction
end BB6.Agent30GeneralFactor
