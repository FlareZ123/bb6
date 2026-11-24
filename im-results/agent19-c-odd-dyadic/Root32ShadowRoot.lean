import Root32ShadowArithmetic
namespace BB6.Agent19Shadow

def rootShadow (a b j : Nat) : Nat := a*(C*j+17300)-C*b

private theorem rootShadow_lift (a b t j e p : Nat)
    (hpos : C*b≤17300*a) (hp : p≤e)
    (he : 17300+C*(t+j)=5*2^e) : 2^p ∣ C*(a*t+b)+rootShadow a b j := by
  have hle : C*b≤a*(C*j+17300) := by
    exact Nat.le_trans hpos (by rw [Nat.mul_comm 17300 a]; exact Nat.mul_le_mul_left a (by omega))
  have hsum : C*(a*t+b)+rootShadow a b j=a*(17300+C*(t+j)) := by
    unfold rootShadow
    have hsub := Nat.sub_add_cancel hle
    simp only [Nat.mul_add] at *
    have h1 : C*(a*t)=a*(C*t) := Nat.mul_left_comm C a t
    omega
  rw [hsum,he,←Nat.mul_assoc]
  exact Nat.dvd_trans (Nat.pow_dvd_pow 2 hp) (Nat.dvd_mul_left _ _)

def dExcluded (f p j : Nat) : Bool := excluded f p (rootShadow 1469153280 393975148 j) (rootShadow 2788638720 747814654 j)
def lExcluded (f p j : Nat) : Bool := excluded f p (rootShadow 5065196640 1358307257 j) (rootShadow 990617040 265648583 j)
def pExcluded (f p j : Nat) : Bool := excluded f p (rootShadow 1376399640 369101882 j) (rootShadow 2835015540 760251268 j)
def threeShadowExcluded (f p j : Nat) : Bool := dExcluded f p j && lExcluded f p j && pExcluded f p j

theorem three_shadow_lift (t j e p : Nat) (hp : p≤e) (he : 17300+C*(t+j)=5*2^e) :
    lift p (rootShadow 1469153280 393975148 j) (rootShadow 2788638720 747814654 j) (1469153280*t+393975148) (2788638720*t+747814654) ∧
    lift p (rootShadow 5065196640 1358307257 j) (rootShadow 990617040 265648583 j) (5065196640*t+1358307257) (990617040*t+265648583) ∧
    lift p (rootShadow 1376399640 369101882 j) (rootShadow 2835015540 760251268 j) (1376399640*t+369101882) (2835015540*t+760251268) := by
  unfold lift
  exact ⟨⟨rootShadow_lift _ _ _ _ _ _ (by decide) hp he,rootShadow_lift _ _ _ _ _ _ (by decide) hp he⟩,
    ⟨rootShadow_lift _ _ _ _ _ _ (by decide) hp he,rootShadow_lift _ _ _ _ _ _ (by decide) hp he⟩,
    ⟨rootShadow_lift _ _ _ _ _ _ (by decide) hp he,rootShadow_lift _ _ _ _ _ _ (by decide) hp he⟩⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem first_root_shadow_checked : threeShadowExcluded 100 256 0=true := by decide
#print axioms excluded_sound
#print axioms three_shadow_lift
#print axioms first_root_shadow_checked

private theorem rootShadow_seed_lift (a b t j0 j e m s : Nat)
    (hpos : C*b≤17300*a) (ha : 2^s∣a) (hj : j0≤j)
    (hc : 2^m∣j-j0) (hp : m+s≤e)
    (he : 17300+C*(t+j)=5*2^e) :
    2^(m+s)∣C*(a*t+b)+rootShadow a b j0 := by
  have h1 := rootShadow_lift a b t j e (m+s) hpos hp he
  have hle : C*b≤a*(C*j0+17300) :=
    Nat.le_trans hpos (by rw [Nat.mul_comm 17300 a]; exact Nat.mul_le_mul_left a (by omega))
  have hle' : C*b≤a*(C*j+17300) :=
    Nat.le_trans hpos (by rw [Nat.mul_comm 17300 a]; exact Nat.mul_le_mul_left a (by omega))
  have heq : rootShadow a b j=rootShadow a b j0+a*C*(j-j0) := by
    unfold rootShadow
    have hJ : j=j0+(j-j0) := by omega
    have hmul : a*(C*j+17300)=a*(C*j0+17300)+a*C*(j-j0) := by
      conv => lhs; rw [hJ]
      simp only [Nat.mul_add,←Nat.mul_assoc]
      omega
    omega
  have hd : 2^(m+s)∣a*C*(j-j0) := by
    rw [Nat.pow_add,Nat.mul_comm (2^m),Nat.mul_assoc]
    exact Nat.mul_dvd_mul ha (Nat.dvd_trans hc (Nat.dvd_mul_left _ _))
  rw [heq,←Nat.add_assoc] at h1
  exact (Nat.dvd_add_iff_left hd).mpr h1

/-- Actual root residuals are huge independently of the seed modulus. -/
theorem three_root_large (t j e : Nat)
    (he13 : 13≤e) (hj : C*j+17300≤e+1)
    (he : 17300+C*(t+j)=5*2^e) :
    RightLarge e (2788638720*t+747814654) ∧
    RightLarge e (990617040*t+265648583) ∧
    RightLarge e (2835015540*t+760251268) := by
  have hPow : C*j+17300≤2^e := Nat.le_trans hj (by have := Nat.lt_pow_self (n:=e) (a:=2) (by decide); omega)
  have hT : 4*2^e≤C*t := by simp only [C] at *; omega
  have hEq : 2^(e-13)*8192=2^e := by simpa using Nat.pow_sub_mul_pow 2 he13
  have hBound : 2^e≤8192*t := by simp only [C] at *; omega
  simp only [RightLarge]
  omega

/-- The residual slopes have minimum valuations 14, 4, and 2.
    These extra bits are available for free from the common index modulus. -/
def threeCylinderExcluded (f m j0 : Nat) : Bool :=
  modExcluded f (m+14) (rootShadow 1469153280 393975148 j0) (rootShadow 2788638720 747814654 j0) &&
  modExcluded f (m+4) (rootShadow 5065196640 1358307257 j0) (rootShadow 990617040 265648583 j0) &&
  modExcluded f (m+2) (rootShadow 1376399640 369101882 j0) (rootShadow 2835015540 760251268 j0)

theorem three_cylinder_lift (t j0 j e m : Nat)
    (hj : j0≤j) (hc : 2^m∣j-j0) (hp : m+14≤e)
    (he : 17300+C*(t+j)=5*2^e) :
    lift (m+14) (rootShadow 1469153280 393975148 j0) (rootShadow 2788638720 747814654 j0) (1469153280*t+393975148) (2788638720*t+747814654) ∧
    lift (m+4) (rootShadow 5065196640 1358307257 j0) (rootShadow 990617040 265648583 j0) (5065196640*t+1358307257) (990617040*t+265648583) ∧
    lift (m+2) (rootShadow 1376399640 369101882 j0) (rootShadow 2835015540 760251268 j0) (1376399640*t+369101882) (2835015540*t+760251268) := by
  unfold lift
  exact ⟨⟨rootShadow_seed_lift _ _ _ _ _ _ _ _ (by decide) (by decide) hj hc hp he,
           rootShadow_seed_lift _ _ _ _ _ _ _ _ (by decide) (by decide) hj hc hp he⟩,
         ⟨rootShadow_seed_lift _ _ _ _ _ _ _ _ (by decide) (by decide) hj hc (by omega) he,
           rootShadow_seed_lift _ _ _ _ _ _ _ _ (by decide) (by decide) hj hc (by omega) he⟩,
         ⟨rootShadow_seed_lift _ _ _ _ _ _ _ _ (by decide) (by decide) hj hc (by omega) he,
           rootShadow_seed_lift _ _ _ _ _ _ _ _ (by decide) (by decide) hj hc (by omega) he⟩⟩

#print axioms three_root_large
#print axioms three_cylinder_lift

end BB6.Agent19Shadow
