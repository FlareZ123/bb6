import Std
namespace BB6.Agent50DyadicWidth

theorem odd_slope_step (b h t : Nat) (hb : b % 2 = 1) :
    (8 * 2^(h+t+1) + b) % 2 = 1 := by omega

theorem odd_root_slope (u h : Nat) (hu : u % 2 = 1) :
    (8 * 2^h + u) % 2 = 1 := by omega

theorem bit_flip (a b r p : Nat) (hp : 0 < p) (hb : b % 2 = 1) :
    ((a + b*(r+p))/p) % 2 = 1 - ((a+b*r)/p)%2 := by
  have heq : (a + b*(r+p))/p = (a+b*r)/p + b := by
    rw [Nat.mul_add, ← Nat.add_assoc, Nat.add_mul_div_right (a+b*r) b hp]
  rw [heq]
  omega

#print axioms odd_slope_step
#print axioms odd_root_slope
#print axioms bit_flip

theorem scaled_div (a b r p s v : Nat) (hp : 0 < p)
    (heq : a + b*r = p*v) :
    (a + b*(r+2*p*s))/p = v+2*b*s := by
  have hmul : a + b*(r+2*p*s) = p*(v+2*b*s) := by
    calc
      a + b*(r+2*p*s) = (a+b*r) + p*(2*b*s) := by
        simp only [Nat.mul_add, Nat.add_assoc]
        simp only [Nat.mul_comm, Nat.mul_left_comm]
      _ = p*(v+2*b*s) := by rw [heq, Nat.mul_add]
  rw [hmul]
  exact Nat.mul_div_cancel_left (v+2*b*s) hp

#print axioms scaled_div

theorem child_affine (q H r p s side m t a b v : Nat) (hp : 0 < p)
    (heq : a + b*r = p*v)
    (hodd : (16*(q+H*r)+side+m+t+v)%2=1) :
    (16*(q+H*(r+2*p*s))+side+m+t+(a+b*(r+2*p*s))/p-1)/2 =
    (16*(q+H*r)+side+m+t+v-1)/2 + (16*H*p+b)*s := by
  have hdiv := scaled_div a b r p s v hp heq
  have he :
      16*(q+H*(r+2*p*s))+side+m+t+(a+b*(r+2*p*s))/p =
      (16*(q+H*r)+side+m+t+v)+2*((16*H*p+b)*s) := by
    rw [hdiv]
    simp only [Nat.mul_add, Nat.add_mul]
    ac_rfl
  rw [he]
  omega

#print axioms child_affine
end BB6.Agent50DyadicWidth
