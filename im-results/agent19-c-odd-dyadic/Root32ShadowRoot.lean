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
end BB6.Agent19Shadow
