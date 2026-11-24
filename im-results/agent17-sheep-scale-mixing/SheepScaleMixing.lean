import SheepEven

namespace SheepScaleMixing
open SheepEven

/-- An arithmetic-progression lift of any genuine generic even-return
witness. Every shifted edge has the same a,h and expands to h+1 real
section steps. Choosing d to be an even multiple of m preserves both
endpoints modulo m. -/
theorem generic_lift (a h u v d : Nat)
    (hu : u % 2 = 1) (hu5 : 5 ≤ u) (hv : v % 2 = 1)
    (hd : d % 2 = 0)
    (he : 2^a*u + a + (u-1)/2 = 1+2^h*v) :
    Steps (h+1) (2^a*u + 2^(a+h+1)*d)
      (1+3^h*v + 3^h*(2^(a+1)+1)*d) := by
  let k := 2^h*d
  let u' := u+2*k
  let v' := v+(2^(a+1)+1)*d
  have hu' : u'%2=1 := by simp [u', Nat.add_mod, hu]
  have hu'5 : 5≤u' := by dsimp [u']; omega
  have hv' : v'%2=1 := by simp [v', Nat.add_mod, Nat.mul_mod, hv, hd]
  have hx : 2^a*u' = 2^a*u + 2^(a+h+1)*d := by
    dsimp [u', k]
    simp only [Nat.mul_add, Nat.pow_succ, Nat.pow_add]
    ac_rfl
  have hhalf : (u'-1)/2 = (u-1)/2 + k := by
    dsimp [u']
    have heq : u+2*k-1 = (u-1)+2*k := by omega
    rw [heq, Nat.add_mul_div_left _ _ (by decide : 0<2)]
  have hfactor : 2^(a+h+1)*d + k = 2^h*((2^(a+1)+1)*d) := by
    dsimp [k]
    simp only [Nat.pow_succ, Nat.pow_add, Nat.mul_add, Nat.add_mul, Nat.one_mul]
    ac_rfl
  have hz : 2^a*u' + a + (u'-1)/2 = 1+2^h*v' := by
    rw [hx, hhalf]
    calc
      2^a*u + 2^(a+h+1)*d + a + ((u-1)/2+k)
          = (2^a*u+a+(u-1)/2)+(2^(a+h+1)*d+k) := by ac_rfl
      _ = (1+2^h*v)+2^h*((2^(a+1)+1)*d) := by rw [he,hfactor]
      _ = 1+2^h*v' := by simp [v', Nat.mul_add, Nat.add_assoc]
  have hfirst := Step.generic a u' hu' hu'5
  rw [hz] at hfirst
  have hlarge : 5 ≤ 1+2^h*v' := by
    rw [← hz]
    have hp : 1≤2^a := Nat.pow_pos (by decide)
    have hm := Nat.mul_le_mul_right u' hp
    simp only [Nat.one_mul] at hm
    omega
  have ht := odd_block h v' (Or.inr hlarge)
  have hsteps := Steps.cons hfirst ht
  rw [hx] at hsteps
  have hy : 1+3^h*v' = 1+3^h*v + 3^h*(2^(a+1)+1)*d := by
    dsimp [v']
    rw [Nat.mul_add]
    ac_rfl
  rw [hy] at hsteps
  exact hsteps

/-- The exact a=1,h=0 corridor on the entire arithmetic progression.
The parameter v is even and at least four, so the source has odd
cofactor 2*v-1 >= 7. -/
theorem corridor_step (v : Nat) (hv : 4≤v) (he : v%2=0) :
    Step (4*v-2) (5*v-2) := by
  have hu : (2*v-1)%2=1 := by omega
  have hl : 5≤2*v-1 := by omega
  have h := Step.generic 1 (2*v-1) hu hl
  simp only [Nat.pow_one] at h
  have hx : 2*(2*v-1) = 4*v-2 := by omega
  rw [hx] at h
  -- target equality after rewriting source expression
  have hy' : (4*v-2)+1+((2*v-1)-1)/2 = 5*v-2 := by omega
  rwa [hy'] at h

/-- All-length corridor, with every intermediate source even and generic. -/
theorem corridor (k v : Nat) (hv : 4≤v) (he : v%2=0) :
    Steps k (4^k*v-2) (5^k*v-2) := by
  induction k generalizing v with
  | zero => simpa using Steps.nil (v-2)
  | succ k ih =>
      have hp : 1≤4^k := Nat.pow_pos (by decide)
      have hv' : 4≤4^k*v := by
        have hm := Nat.mul_le_mul_right v hp
        simp only [Nat.one_mul] at hm
        omega
      have he' : (4^k*v)%2=0 := by simp [Nat.mul_mod, he]
      have first := corridor_step (4^k*v) hv' he'
      have hstart : 4*(4^k*v) = 4^(k+1)*v := by
        simp only [Nat.pow_succ]; ac_rfl
      have hmid : 5*(4^k*v) = 4^k*(5*v) := by ac_rfl
      rw [hstart,hmid] at first
      have tail := ih (5*v) (by omega) (by simp [Nat.mul_mod, he])
      have hend : 5^k*(5*v) = 5^(k+1)*v := by
        simp only [Nat.pow_succ]; ac_rfl
      rw [hend] at tail
      exact Steps.cons first tail

/-- The a=2,h=0 corridor: shift by 12, multiply by 9/8. -/
theorem corridor2_step (v : Nat) (hv : 4≤v) (he : v%2=0) :
    Step (8*v-12) (9*v-12) := by
  have hu : (2*v-3)%2=1 := by omega
  have hl : 5≤2*v-3 := by omega
  have h := Step.generic 2 (2*v-3) hu hl
  have hx : 2^2*(2*v-3) = 8*v-12 := by omega
  rw [hx] at h
  have hy : (8*v-12)+2+((2*v-3)-1)/2 = 9*v-12 := by omega
  rwa [hy] at h

theorem corridor2 (k v : Nat) (hv : 4≤v) (he : v%2=0) :
    Steps k (8^k*v-12) (9^k*v-12) := by
  induction k generalizing v with
  | zero => simpa using Steps.nil (v-12)
  | succ k ih =>
      have hp : 1≤8^k := Nat.pow_pos (by decide)
      have hv' : 4≤8^k*v := by
        have hm := Nat.mul_le_mul_right v hp
        simp only [Nat.one_mul] at hm
        omega
      have he' : (8^k*v)%2=0 := by simp [Nat.mul_mod, he]
      have first := corridor2_step (8^k*v) hv' he'
      have hstart : 8*(8^k*v) = 8^(k+1)*v := by
        simp only [Nat.pow_succ]; ac_rfl
      have hmid : 9*(8^k*v) = 8^k*(9*v) := by ac_rfl
      rw [hstart,hmid] at first
      have tail := ih (9*v) (by omega) (by simp [Nat.mul_mod, he])
      have hend : 9^k*(9*v) = 9^(k+1)*v := by
        simp only [Nat.pow_succ]; ac_rfl
      rw [hend] at tail
      exact Steps.cons first tail

end SheepScaleMixing
#print axioms SheepScaleMixing.generic_lift
#print axioms SheepScaleMixing.corridor_step
#print axioms SheepScaleMixing.corridor
#print axioms SheepScaleMixing.corridor2_step
#print axioms SheepScaleMixing.corridor2
