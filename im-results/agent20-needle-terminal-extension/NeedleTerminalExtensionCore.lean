import Std
set_option exponentiation.threshold 1024

namespace NeedleTerminalExtension

/-- Inverse branch parameter v is the exact source dyadic valuation. -/
def den (v : Nat) : Nat := 2^(v+1)+3
def mul (v : Nat) : Int := 2^(v+1)
def add (v : Nat) : Int := (2:Int)^v*(3-2*(v:Int))

def Edge (v x y : Nat) : Prop :=
  ∃ q : Nat, x=2^v*(2*q+3) ∧ y=x+v+3*(q+1)

theorem den_odd (v : Nat) : den v % 2=1 := by
  simp [den,Nat.pow_succ,Nat.add_mod]

theorem den_pos (v : Nat) : 0<den v := by simp [den]

theorem odd_cancel_pow (D v : Nat) (z : Int) (hodd : D%2=1)
    (h : (D:Int) ∣ (2:Int)^v*z) : (D:Int) ∣ z := by
  have hc : D.Coprime 2 := by
    unfold Nat.Coprime
    rw [Nat.gcd_comm,Nat.gcd_rec,hodd]
    decide
  apply Int.natAbs_dvd_natAbs.mp
  have hn := Int.natAbs_dvd_natAbs.mpr h
  rw [Int.natAbs_mul, Int.natAbs_pow] at hn
  simp at hn ⊢
  exact (hc.pow_right v).dvd_of_dvd_mul_left hn

theorem inverse_sound (v x y : Nat) (hx : 3*2^v≤x)
    (he : (den v:Int)*(x:Int)=mul v*(y:Int)+add v) : Edge v x y := by
  have hpow : (2:Int)^(v+1)=2*(2:Int)^v := by rw [Int.pow_succ,Int.mul_comm]
  have he' : (den v:Int)*(x:Int)=(2:Int)^v*(2*(y:Int)+3-2*(v:Int)) := by
    simp only [mul,add,hpow] at he
    grind
  have hd : (den v:Int) ∣ (2:Int)^v*(2*(y:Int)+3-2*(v:Int)) := ⟨x,he'.symm⟩
  obtain ⟨z,hz⟩ := odd_cancel_pow (den v) v _ (den_odd v) hd
  have hx' : (x:Int)=(2:Int)^v*z := by
    apply (Int.mul_eq_mul_left_iff (show (den v:Int)≠0 by have := den_pos v; omega)).mp
    grind
  have hp : 0<(2:Int)^v := Int.pow_pos (by decide)
  have hl : (3:Int)*(2:Int)^v≤(x:Int) := by exact_mod_cast hx
  have hz3 : 3≤z := by
    exact Int.le_of_mul_le_mul_left (show (2:Int)^v*3≤(2:Int)^v*z by grind) hp
  have hzodd : z%2=1 := by
    have hdodd : (den v:Int)%2=1 := by exact_mod_cast den_odd v
    have h1 : (2*(y:Int)+3-2*(v:Int))%2=1 := by omega
    have h2 : ((den v:Int)*z)%2=z%2 := by rw [Int.mul_emod,hdodd]; omega
    rw [hz,h2] at h1
    exact h1
  let q : Nat := ((z-3)/2).toNat
  have hq : (q:Int)=(z-3)/2 := Int.toNat_of_nonneg (by omega)
  have hzq : z=2*(q:Int)+3 := by omega
  refine ⟨q,?_,?_⟩
  · have h : (x:Int)=(2:Int)^v*(2*(q:Int)+3) := by rw [hx',hzq]
    exact_mod_cast h
  · have hd' : (den v:Int)=2*(2:Int)^v+3 := by simp [den,hpow]
    have hy : (y:Int)=(x:Int)+(v:Int)+3*((q:Int)+1) := by
      rw [hd',hzq] at hz
      rw [hzq] at hx'
      grind
    exact_mod_cast hy

theorem inverse_complete (v x y : Nat) (h : Edge v x y) :
    3*2^v≤x ∧ (den v:Int)*(x:Int)=mul v*(y:Int)+add v := by
  obtain ⟨q,hx,hy⟩ := h
  have hq : (3:Nat)≤2*q+3 := by omega
  refine ⟨?_,?_⟩
  · rw [hx,Nat.mul_comm 3]
    exact Nat.mul_le_mul_left _ hq
  · have hx' : (x:Int)=(2:Int)^v*(2*(q:Int)+3) := by exact_mod_cast hx
    have hy' : (y:Int)=(x:Int)+(v:Int)+3*((q:Int)+1) := by exact_mod_cast hy
    have hp : (2:Int)^(v+1)=2*(2:Int)^v := by rw [Int.pow_succ,Int.mul_comm]
    simp [den,mul,add,hp]
    grind

/-- Composition U(y)=(A*y+C)/D in reverse-time order. -/
structure Aff where
  A : Int
  C : Int
  D : Nat
  deriving DecidableEq, Repr

def identity : Aff := ⟨1,0,1⟩
def Aff.append (u : Aff) (v : Nat) : Aff :=
  ⟨mul v*u.A,mul v*u.C+add v*(u.D:Int),u.D*den v⟩
def compose : List Nat → Aff
  | [] => identity
  | v::w => (compose w).append v

/-- The word here is given in forward-time order. -/
def Aff.numerator (u : Aff) (y : Int) : Int := u.A*y+u.C

theorem append_numerator (u : Aff) (v : Nat) (y : Int) :
    (u.append v).numerator y=mul v*u.numerator y+add v*(u.D:Int) := by
  simp [Aff.append,Aff.numerator]; grind

theorem denominator_odd (w : List Nat) : (compose w).D%2=1 := by
  induction w with
  | nil => decide
  | cons v w ih => simp [compose,Aff.append,Nat.mul_mod,ih,den_odd]

theorem prefix_integral (u : Aff) (v : Nat) (y : Int) (hodd : u.D%2=1)
    (h : ((u.append v).D:Int) ∣ (u.append v).numerator y) :
    (u.D:Int) ∣ u.numerator y := by
  have hD : (u.D:Int) ∣ ((u.append v).D:Int) := by
    simp [Aff.append]
  have h1 := Int.dvd_trans hD h
  rw [append_numerator] at h1
  have h2 : (u.D:Int) ∣ add v*(u.D:Int) := Int.dvd_mul_left _ _
  have h3 := Int.dvd_sub h1 h2
  simp only [Int.add_sub_cancel] at h3
  exact odd_cancel_pow u.D (v+1) _ hodd h3

theorem suffix_integral (w : List Nat) (y : Int)
    (h : ((compose w).D:Int) ∣ (compose w).numerator y) :
    ∀ s, s.IsSuffix w → ((compose s).D:Int) ∣ (compose s).numerator y := by
  induction w with
  | nil =>
    intro s hs
    have he : s=[] := by simpa using hs
    subst s
    exact h
  | cons v w ih =>
    intro s hs
    rcases List.suffix_cons_iff.mp hs with hEq | hSuf
    · subst s; exact h
    · exact ih (prefix_integral (compose w) v y (denominator_odd w) h) s hSuf

inductive Path : List Nat → Nat → Nat → Prop
  | nil (x : Nat) : Path [] x x
  | cons {v w x z y} : Edge v x z → Path w z y → Path (v::w) x y

theorem compose_pos (w : List Nat) : 0<(compose w).A ∧ 0<(compose w).D := by
  induction w with
  | nil => decide
  | cons v w ih =>
    simp only [compose,Aff.append]
    exact ⟨Int.mul_pos (Int.pow_pos (by decide)) ih.1,Nat.mul_pos ih.2 (den_pos v)⟩

def Large (w : List Nat) (y : Nat) : Prop :=
  ∀ v s, (v::s).IsSuffix w → (compose (v::s)).numerator y ≥
    ((compose (v::s)).D:Int)*(3*(2:Int)^v)

theorem path_from_integral (w : List Nat) (y : Nat)
    (h : ((compose w).D:Int) ∣ (compose w).numerator y)
    (large : Large w y) :
    ∃ x : Nat, ((compose w).D:Int)*(x:Int)=(compose w).numerator y ∧ Path w x y := by
  induction w with
  | nil => exact ⟨y,by simp [compose,identity,Aff.numerator],Path.nil y⟩
  | cons v w ih =>
    have hw : ((compose w).D:Int) ∣ (compose w).numerator y :=
      prefix_integral (compose w) v y (denominator_odd w) h
    have hl : Large w y := by
      intro a s hs
      exact large a s (List.suffix_cons_iff.mpr (Or.inr hs))
    obtain ⟨z,hz,hpath⟩ := ih hw hl
    obtain ⟨x,hx⟩ := h
    have hD : 0<((compose (v::w)).D:Int) := by exact_mod_cast (compose_pos (v::w)).2
    have hbound := large v w (List.suffix_refl _)
    rw [hx] at hbound
    have hxlow : 3*(2:Int)^v≤x := Int.le_of_mul_le_mul_left hbound hD
    have hxn : 0≤x := by have hp : 0<(2:Int)^v := Int.pow_pos (by decide); omega
    let X := x.toNat
    have hX : (X:Int)=x := Int.toNat_of_nonneg hxn
    refine ⟨X,by rw [hX,hx],Path.cons (inverse_sound v X z ?_ ?_) hpath⟩
    · rw [←hX] at hxlow
      exact_mod_cast hxlow
    · have hp := append_numerator (compose w) v y
      change (compose (v::w)).numerator y = _ at hp
      rw [hx,←hz] at hp
      rw [hX]
      simp only [compose,Aff.append,Int.natCast_mul] at hp
      have hDw : ((compose w).D:Int)≠0 := by have hh := (compose_pos w).2; omega
      apply (Int.mul_eq_mul_left_iff hDw).mp
      grind

theorem large_eventually (w : List Nat) : ∃ B : Nat, ∀ y : Nat, B≤y → Large w y := by
  induction w with
  | nil =>
    refine ⟨0,?_⟩
    intro y hy v s hs
    simp at hs
  | cons v w ih =>
    obtain ⟨B,hB⟩ := ih
    let U := compose (v::w)
    let C := (U.D:Int)*(3*(2:Int)^v)-U.C
    refine ⟨max B C.toNat,?_⟩
    intro y hy a s hs
    rcases List.suffix_cons_iff.mp hs with he | hs
    · have hAy : 1≤U.A := by have h : 0<U.A := (compose_pos (v::w)).1; omega
      have hyC : C≤(y:Int) := by
        have h : C.toNat≤y := Nat.le_trans (Nat.le_max_right _ _) hy
        omega
      have hmul := Int.mul_le_mul_of_nonneg_right hAy (Int.natCast_nonneg y)
      have hEq := List.cons.inj he
      rcases hEq with ⟨rfl,rfl⟩
      change U.D*(3*(2:Int)^a)≤U.A*(y:Int)+U.C
      dsimp [C] at hyC
      omega
    · exact hB y (Nat.le_trans (Nat.le_max_left _ _) hy) a s hs

/-- Inverse m-word 3,2,1,2,1 corresponds to forward valuation word
0,1,0,1,2. Its denominator is 5^2*7^2*11. -/
def seedWord : List Nat := [0,1,0,1,2]
theorem seed_coefficients : compose seedWord = ⟨512,11569,13475⟩ := by decide

theorem seed_power_period : (2:Int)^420%13475=1 := by decide

theorem seed_progression (t : Nat) : (13475:Int) ∣ 512*2^(379+420*t)+11569 := by
  have hp : ∀ t : Nat, (2:Int)^(379+420*t)%13475 = 688 := by
    intro t
    induction t with
    | zero => decide
    | succ t ih =>
      rw [Nat.mul_succ,←Nat.add_assoc,Int.pow_add,Int.mul_emod,ih,seed_power_period]
      decide
  apply Int.dvd_iff_emod_eq_zero.mpr
  rw [Int.add_emod,Int.mul_emod,hp]
  decide

theorem seed_integral (t : Nat) :
    ((compose seedWord).D:Int) ∣ (compose seedWord).numerator (2^(379+420*t)) := by
  rw [seed_coefficients]
  exact seed_progression t

/-- Numerators of the two composed rational inverse maps. Their
commutator provides the translation 3/35 modulo any coprime modulus. -/
theorem translation_pair :
    compose [0,1] = ⟨8,25,35⟩ ∧ compose [1,0] = ⟨8,22,35⟩ := by decide

#print axioms path_from_integral
#print axioms large_eventually
#print axioms inverse_sound
#print axioms inverse_complete
#print axioms suffix_integral
#print axioms seed_integral
#print axioms translation_pair
end NeedleTerminalExtension
