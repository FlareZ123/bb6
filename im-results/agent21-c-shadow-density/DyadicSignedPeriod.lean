import DyadicPeriod
import DyadicReach

namespace BB6.Agent21Dyadic

def signedS (x y : Int) : Int := -x-2*y
def signedZ (x y : Int) : Int := (-x-2-parity (signedS x y))/2

theorem signed_twice_Z (x y : Int) :
    2*signedZ x y=-x-2-parity (signedS x y) := by
  unfold signedZ signedS parity
  omega

theorem signed_mass_shift (x y u v : Int) (n : Nat) :
    signedS (x+P (n+1)*u) (y+P (n+1)*v) =
      signedS x y-2*(P n*(u+2*v)) := by
  have hp : P (n+1)=2*P n := by
    rw [P_add]
    change P n*2=2*P n
    omega
  rw [hp]
  unfold signedS
  have hu : (2*P n)*u=2*(P n*u) := by ac_rfl
  have hv : (2*P n)*v=2*(P n*v) := by ac_rfl
  have hsum : P n*(u+2*v)=P n*u+2*(P n*v) := by
    rw [Int.mul_add]
    congr 1
    ac_rfl
  rw [hu,hv,hsum]
  omega

theorem signed_norm_shift (x y u v : Int) (n : Nat) :
    signedZ (x+P (n+1)*u) (y+P (n+1)*v) =
      signedZ x y-P n*u := by
  have hs := signed_mass_shift x y u v n
  have hpar : parity (signedS (x+P (n+1)*u) (y+P (n+1)*v)) =
      parity (signedS x y) := by
    rw [hs]
    unfold parity
    omega
  have h1 := signed_twice_Z (x+P (n+1)*u) (y+P (n+1)*v)
  have h0 := signed_twice_Z x y
  rw [hpar] at h1
  have hm : P (n+1)*u=2*(P n*u) := by
    rw [P_add]
    change (P n*2)*u=2*(P n*u)
    ac_rfl
  rw [hm] at h1
  omega

theorem positive_head (w : List Nat) (hw : Positive w) (hne : w≠[]) :
    ∃ r t, w=r::t ∧ 0<r := by
  cases w with
  | nil => contradiction
  | cons r t =>
      exact ⟨r,t,rfl,hw r (by simp)⟩

/-- The full completed-or-pending inverse word condition is invariant
    under translating x and y by arbitrary integer multiples of 2^b.
    Unlike the mass coordinate alone, the *combined normalized word
    numerator* is exactly periodic at b bits. -/
theorem signed_open_period (x y u v : Int) (n : Nat) :
    OpenAt (signedS (x+P (n+1)*u) (y+P (n+1)*v))
      (signedZ (x+P (n+1)*u) (y+P (n+1)*v)) (n+1) ↔
    OpenAt (signedS x y) (signedZ x y) (n+1) := by
  rw [signed_mass_shift, signed_norm_shift]
  unfold OpenAt
  constructor
  · rintro (⟨w,hp,hc,hd⟩ | ⟨w,r,hr,hp,hc,hd⟩)
    · have hne : w≠[] := by
        intro hw
        subst w
        simp [cost] at hc
      have hword := positive_head w hp hne
      exact Or.inl ⟨w,hp,hc,(period_word_iff _ _ u v n w hword).mp hd⟩
    · have hword := positive_head (w++[r]) hp (by simp)
      exact Or.inr ⟨w,r,hr,hp,hc,(period_word_iff _ _ u v n (w++[r]) hword).mp hd⟩
  · rintro (⟨w,hp,hc,hd⟩ | ⟨w,r,hr,hp,hc,hd⟩)
    · have hne : w≠[] := by
        intro hw
        subst w
        simp [cost] at hc
      have hword := positive_head w hp hne
      exact Or.inl ⟨w,hp,hc,(period_word_iff _ _ u v n w hword).mpr hd⟩
    · have hword := positive_head (w++[r]) hp (by simp)
      exact Or.inr ⟨w,r,hr,hp,hc,(period_word_iff _ _ u v n (w++[r]) hword).mpr hd⟩

#print axioms signed_open_period
end BB6.Agent21Dyadic
