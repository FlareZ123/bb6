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

/-- Universal dyadic curvature for parity-affine maps with odd drift. -/
theorem iterH_dyadic_curvature (r c s n z : Nat)
    (hodd:r%2=1) (hgap:r≤2*s) :
    (iterH r c s (n+1) z + iterH r c s (n+1) (z+2*2^n)+
      (2*s-r) = 2*iterH r c s (n+1) (z+2^n)) ∨
    (iterH r c s (n+1) z + iterH r c s (n+1) (z+2*2^n) =
      2*iterH r c s (n+1) (z+2^n)+(2*s-r)) := by
  have h1 : iterH r c s n (z+2^n) =
      iterH r c s n z+r^n := by
    simpa using iterH_two_adic_shift r c s n z 1
  have h2 : iterH r c s n (z+2*2^n) =
      iterH r c s n z+2*r^n := by
    simpa [Nat.mul_comm] using iterH_two_adic_shift r c s n z 2
  have hp : (r^n)%2=1 := by simp [Nat.pow_mod,hodd]
  have hc := H_odd_scale_curvature r c s (iterH r c s n z) (r^n)
    hodd hp hgap
  simp only [iterH_succ_last]
  rw [h1,h2]
  rcases hc with ⟨_,he⟩ | ⟨_,he⟩
  · exact Or.inl he
  · exact Or.inr he

private theorem affine_second_mod (m a b x t : Nat) (f : Nat → Nat)
    (h : ∀ z, f z % m = (a*z+b)%m) :
    (f x + f (x+2*t)) % m = (2*f (x+t)) % m := by
  have hlinear : a*x+b + (a*(x+2*t)+b) =
      2*(a*(x+t)+b) := by
    have htwice : a*(2*t)=2*(a*t) := by ac_rfl
    rw [Nat.mul_add a x (2*t), htwice]
    simp [Nat.mul_add]
    omega
  calc
    (f x + f (x+2*t)) % m =
        (f x % m + f (x+2*t)%m)%m := Nat.add_mod _ _ _
    _ = ((a*x+b)%m + (a*(x+2*t)+b)%m)%m := by
      rw [h x,h (x+2*t)]
    _ = (a*x+b + (a*(x+2*t)+b))%m :=
      (Nat.add_mod _ _ _).symm
    _ = (2*(a*(x+t)+b))%m := by rw [hlinear]
    _ = (2%m * ((a*(x+t)+b)%m))%m := Nat.mul_mod _ _ _
    _ = (2%m * (f (x+t)%m))%m := by rw [h (x+t)]
    _ = (2*f (x+t))%m := (Nat.mul_mod _ _ _).symm

end BB6.Agent30Generic
