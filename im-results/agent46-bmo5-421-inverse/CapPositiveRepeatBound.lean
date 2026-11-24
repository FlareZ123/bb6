import CapPositiveRepeat

namespace CapSieve.Repeat

def Delta (m : Nat) (q : Nat → Int) (i : Nat) : Int := q (i+m)-(2:Int)^m*q i

def Defect (m : Nat) (q : Nat → Int) (i : Nat) : Int := Delta m q (i+m)-Delta m q i

theorem delta_step {m s i : Nat} {q : Nat → Int} {a : Nat → Nat}
    (hr : Recurrence s q a) (hi : s≤i) (ha : a (i+m)=a i) :
    Delta m q (i+1)=(3:Int)^(a i)*Delta m q i-3*((2:Int)^m-1) := by
  have e1 := (hr i hi).2
  have e2 := (hr (i+m) (by omega)).2
  rw [show i+m+1=i+1+m by omega,ha,Int.pow_add] at e2
  unfold Delta
  rw [e1,e2]
  simp only [Int.mul_sub,Int.mul_add]
  have h1 : (2:Int)^m*((3:Int)^(a i)*q i)=(3:Int)^(a i)*((2:Int)^m*q i) := by ac_rfl
  have h2 : (2:Int)^m*(10*(2:Int)^i)=10*((2:Int)^i*(2:Int)^m) := by ac_rfl
  have h3 : (2:Int)^m*3=3*(2:Int)^m := by ac_rfl
  rw [h1,h2,h3]
  omega

theorem defect_step {m s i : Nat} {q : Nat → Int} {a : Nat → Nat}
    (hr : Recurrence s q a) (hi : s≤i)
    (ha : a (i+m)=a i) (hb : a (i+m+m)=a (i+m)) :
    Defect m q (i+1)=(3:Int)^(a i)*Defect m q i := by
  have h1 := delta_step hr hi ha
  have h2 := delta_step hr (show s≤i+m by omega) hb
  rw [ha,show i+m+1=i+1+m by omega] at h2
  unfold Defect
  rw [h1,h2]
  simp only [Int.mul_sub]
  omega

/-- Construct the periodic packet from two equal exponent blocks and zero
    affine defect. Alignment to a multiple of m simplifies cyclic indexing. -/
theorem packet_of_zero_defect {m s k : Nat} {q : Nat → Int} {a : Nat → Nat}
    (hm : 0<m) (hr : Recurrence s q a) (hk : s≤k) (ha : k%m=0)
    (hrep : ∀ i, k≤i → i<k+m → a (i+m)=a i)
    (hz : Defect m q k=0) : ∃ p : Period m, At p q a k := by
  let b := fun i => a (k+i%m)
  let d := fun i => Delta m q (k+i%m)
  have hb : ∀ i, b (i+m)=b i := by intro i; simp [b,Nat.add_mod_right]
  have hd : ∀ i, d (i+m)=d i := by intro i; simp [d,Nat.add_mod_right]
  have hds : ∀ i, d (i+1)=(3:Int)^(b i)*d i-3*((2:Int)^m-1) := by
    intro i
    let r := i%m
    have hrange : r<m := Nat.mod_lt _ hm
    have hmod : (i+1)%m=(r+1)%m := by rw [←Nat.mod_add_mod]
    have hst := delta_step hr (show s≤k+r by omega) (hrep (k+r) (by omega) (by omega))
    change Delta m q (k+(i+1)%m)=(3:Int)^(a (k+r))*Delta m q (k+r)-3*((2:Int)^m-1)
    rw [←hst,hmod]
    by_cases he : r+1<m
    · rw [Nat.mod_eq_of_lt he]; congr 1
    · have hrm : r+1=m := by omega
      rw [hrm,Nat.mod_self,show k+0=k by omega,show k+r+1=k+m by omega]
      unfold Defect at hz
      omega
  have hdu : ∀ i, d i%3=0 := by
    have hsucc : ∀ i, d (i+1)%3=0 := by
      intro i
      have hpos := (hr (k+i%m) (by omega)).1
      change 0<b i at hpos
      rw [hds]
      cases hA : b i with
      | zero => omega
      | succ v => rw [Int.pow_succ,show (3:Int)^v*3*d i=3*((3:Int)^v*d i) by ac_rfl]; omega
    intro i
    cases i with
    | zero => have h1 := hsucc (m-1); rw [show m-1+1=0+m by omega,hd] at h1; exact h1
    | succ i => exact hsucc i
  let p : Period m := ⟨b,d,hb,hd,hds,hdu⟩
  refine ⟨p,?_⟩
  constructor
  · change q (k+m)=(2:Int)^m*q k+Delta m q (k+k%m)
    rw [ha,Nat.add_zero]; unfold Delta; omega
  · intro i hi hi'
    let r := i-k
    have hir : i=k+r := by dsimp [r]; omega
    have hrl : r<m := by omega
    change a i=a (k+i%m)
    have hm' : i%m=r := by rw [hir,Nat.add_mod,ha,Nat.mod_eq_of_lt hrl,Nat.zero_add,Nat.mod_eq_of_lt hrl]
    rw [hm',←hir]

def RootSeed (s : Nat) (q : Nat → Int) : Prop :=
  (s=0 ∧ q 0=6) ∨ (s=0 ∧ q 0=8) ∨ (s=1 ∧ q 1=15)

theorem no_zero_defect {m s k : Nat} {q : Nat → Int} {a : Nat → Nat}
    (hm : 4≤m) (hr : Recurrence s q a) (hseed : RootSeed s q) (hk : s+1≤k)
    (ha : k%m=0) (hrep : ∀ i, k≤i → i<k+m → a (i+m)=a i) : Defect m q k≠0 := by
  intro hz
  obtain ⟨p,hp⟩ := packet_of_zero_defect (by omega) hr (by omega) ha hrep hz
  rcases hseed with ⟨rfl,h⟩|⟨rfl,h⟩|⟨rfl,h⟩
  · exact no_packet_seed_six (by omega) hr h hk hp
  · exact no_packet_seed_eight (by omega) hr h hk hp
  · exact no_packet_seed_fifteen hm hr h hk hp

/-- Growth of the integer second affine difference along a repeated word. -/
theorem defect_growth {m s k n : Nat} {q : Nat → Int} {a : Nat → Nat}
    (hr : Recurrence s q a) (hk : s≤k) (hz : Defect m q k≠0)
    (hrep : ∀ i, k≤i → i<k+n+m → a (i+m)=a i) :
    3^n≤(Defect m q (k+n)).natAbs := by
  induction n with
  | zero => simp only [Nat.add_zero,Nat.pow_zero]; exact Int.natAbs_pos.mpr hz
  | succ n ih =>
    have h0 := ih (by intro i hi hi'; exact hrep i hi (by omega))
    have h1 := defect_step hr (show s≤k+n by omega)
      (hrep (k+n) (by omega) (by omega)) (hrep (k+n+m) (by omega) (by omega))
    have hpos := (hr (k+n) (by omega)).1
    rw [show k+(n+1)=k+n+1 by omega,h1,Int.natAbs_mul,Int.natAbs_pow]
    change 3^(n+1)≤3^(a (k+n))*(Defect m q (k+n)).natAbs
    rw [Nat.pow_succ]
    have ha : 3≤3^(a (k+n)) := by simpa using Nat.pow_le_pow_right (by decide : 0<3) (show 1≤a (k+n) by omega)
    rw [Nat.mul_comm (3^n) 3]
    exact Nat.mul_le_mul ha h0

/-- Uniform bound on the second affine difference of a bounded relaxed orbit. -/
theorem defect_upper {m s i : Nat} {q : Nat → Int}
    (hq : ∀ j, s≤j → 0≤q j ∧ q j≤10*(2:Int)^j) (hi : s≤i) :
    (Defect m q i).natAbs≤20*2^(i+m+m) := by
  have h0 := hq i hi
  have h1 := hq (i+m) (by omega)
  have h2 := hq (i+m+m) (by omega)
  let R : Int := (2:Int)^m
  let P : Int := (2:Int)^i
  have hR : 1≤R := Int.pow_pos (by decide)
  have hP : 0≤P := Int.le_of_lt (Int.pow_pos (by decide))
  have he1 : (2:Int)^(i+m)=P*R := by dsimp [P,R]; rw [Int.pow_add]
  have he2 : (2:Int)^(i+m+m)=P*R*R := by rw [Int.pow_add,he1]
  rw [he1] at h1
  rw [he2] at h2
  have hR1 := Int.mul_nonneg (show 0≤R by omega) h0.1
  have hR2 := Int.mul_nonneg (show 0≤R by omega) h1.1
  have hB1 := Int.mul_le_mul_of_nonneg_left h0.2 (show 0≤R by omega)
  have hB2 := Int.mul_le_mul_of_nonneg_left h1.2 (show 0≤R by omega)
  have hPR : 0≤P*R := Int.mul_nonneg hP (by omega)
  have hPRle : P*R≤P*R*R := by
    have h := Int.mul_le_mul_of_nonneg_left hR hPR
    simpa using h
  have hN1 : R*(10*P)=10*(P*R) := by ac_rfl
  have hN2 : R*(10*(P*R))=10*(P*R*R) := by ac_rfl
  rw [hN1] at hB1; rw [hN2] at hB2
  have hD : Defect m q i=q (i+m+m)-R*q (i+m)-q (i+m)+R*q i := by
    unfold Defect Delta; dsimp [R]; omega
  have hlow : -(20*(P*R*R))≤Defect m q i := by rw [hD]; omega
  have hhigh : Defect m q i≤20*(P*R*R) := by rw [hD]; omega
  have he : ((20*2^(i+m+m):Nat):Int)=20*(P*R*R) := by
    simp only [Int.natCast_mul,Int.natCast_pow]
    change (20:Int)*(2:Int)^(i+m+m)=20*(P*R*R)
    rw [he2]
  omega

/-- A simple effective domination of powers: 3^(2t) >= 2^(3t). -/
theorem pow32 (t : Nat) : 2^(3*t)≤3^(2*t) := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [show 3*(t+1)=3*t+3 by omega,show 2*(t+1)=2*t+2 by omega,Nat.pow_add,Nat.pow_add]
    exact Nat.mul_le_mul ih (by decide)

theorem repeat_bound_aligned {m s k n : Nat} {q : Nat → Int} {a : Nat → Nat}
    (hm : 4≤m) (hr : Recurrence s q a) (hseed : RootSeed s q) (hk : s+1≤k)
    (halign : k%m=0) (hq : ∀ j, s≤j → 0≤q j ∧ q j≤10*(2:Int)^j)
    (hrep : ∀ i, k≤i → i<k+n+m → a (i+m)=a i) : n<2*(k+2*m+5)+2 := by
  have hz := no_zero_defect hm hr hseed hk halign (by intro i hi hi'; exact hrep i hi (by omega))
  have hlo := defect_growth hr (show s≤k by omega) hz hrep
  have hhi := defect_upper (m:=m) hq (show s≤k+n by omega)
  let t := n/2
  have htn : 2*t≤n := by dsimp [t]; omega
  have hpow := Nat.pow_le_pow_right (by decide : 0<3) htn
  have hp := pow32 t
  have hres : 2^(3*t)≤20*2^(k+n+m+m) := Nat.le_trans hp (Nat.le_trans hpow (Nat.le_trans hlo hhi))
  have hres' : 2^(3*t) < 2^(k+n+m+m+5) := by
    apply Nat.lt_of_le_of_lt hres
    rw [Nat.pow_add 2 (k+n+m+m) 5,show 2^5=32 by decide,Nat.mul_comm 20]
    exact Nat.mul_lt_mul_of_pos_left (by decide : 20<32) (Nat.two_pow_pos _)
  have hlt : 3*t<k+n+m+m+5 := by
    by_cases he : 3*t<k+n+m+m+5
    · exact he
    · have hge := Nat.pow_le_pow_right (by decide : 0<2) (show k+n+m+m+5≤3*t by omega)
      omega
  dsimp [t] at *
  omega

#print axioms packet_of_zero_defect
#print axioms repeat_bound_aligned
end CapSieve.Repeat
