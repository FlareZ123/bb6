import PeriodicReset
namespace CascadePeriodic

abbrev Token := Nat × Nat
structure Coeff where
  p : Int
  r : Int
  s : Int
  c : Int
  e : Int
  d : Nat
  deriving Repr

def coeff : List Token → Coeff
  | [] => ⟨1,1,0,0,0,0⟩
  | (a,δ)::w =>
    let q := coeff w
    let p : Int := 2^(a+1)
    let r : Int := 3^a
    ⟨q.p*p, q.r*r, q.r*r+p*q.s*2^δ,
     2*q.r*r+p*q.c, 5*q.r*r+p*q.c*(δ:Int)+p*q.e, δ+q.d⟩

inductive Follows : List Token → Int → Nat → Int → Nat → Prop where
  | nil (x : Int) (k : Nat) : Follows [] x k x k
  | cons {a δ k l : Nat} {w : List Token} {x y z : Int} :
      2^(a+1)*y=3^a*(x+16*2^k+2*(k:Int)+5) →
      Follows w y (k+δ) z l → Follows ((a,δ)::w) x k z l

theorem follows_affine {w : List Token} {x y : Int} {k l : Nat}
    (hf : Follows w x k y l) :
    l=k+(coeff w).d ∧
    (coeff w).p*y=(coeff w).r*x+16*(coeff w).s*2^k+(coeff w).c*(k:Int)+(coeff w).e := by
  induction hf with
  | nil x k => simp [coeff]
  | @cons a δ k l w x y z he hf ih =>
    obtain ⟨hl,ha⟩ := ih
    constructor
    · simp only [coeff]
      omega
    · simp only [coeff]
      rw [Int.pow_add,Int.natCast_add] at ha
      have hmul : (2:Int)^(a+1)*((coeff w).p*z) =
          (2:Int)^(a+1)*((coeff w).r*y+16*(coeff w).s*(2^k*2^δ)+
            (coeff w).c*((k:Int)+(δ:Int))+(coeff w).e) := congrArg (fun v => (2:Int)^(a+1)*v) ha
      clear hf hl
      grind

private theorem two_pow_even (a : Nat) : ((2:Int)^(a+1))%2=0 := by
  rw [Int.pow_succ,Int.mul_emod]
  simp

private theorem three_pow_odd (a : Nat) : ((3:Int)^a)%2=1 := by
  induction a with
  | zero => decide
  | succ a ih => rw [Int.pow_succ,Int.mul_emod,ih] <;> decide

theorem coeff_r_odd (w : List Token) : (coeff w).r%2=1 := by
  induction w with
  | nil => decide
  | cons a w ih =>
    rcases a with ⟨a,δ⟩
    simp only [coeff]
    rw [Int.mul_emod,ih,three_pow_odd] <;> decide

theorem coeff_nonempty_parity (a δ : Nat) (w : List Token) :
    (coeff ((a,δ)::w)).p%2=0 ∧ (coeff ((a,δ)::w)).s%2=1 := by
  simp only [coeff]
  constructor
  · rw [Int.mul_emod,two_pow_even]
    simp
  · rw [Int.add_emod,Int.mul_emod (coeff w).r,coeff_r_odd,three_pow_odd]
    have hzero : ((2:Int)^(a+1)*(coeff w).s*2^δ)%2=0 := by
      rw [Int.mul_emod,Int.mul_emod ((2:Int)^(a+1)),two_pow_even]
      simp
    rw [hzero] <;> decide

theorem repeated_word_rigidity (a δ : Nat) (w : List Token)
    (x : Nat → Int) (k : Nat → Nat)
    (hf : ∀ j, Follows ((a,δ)::w) (x j) (k j) (x (j+1)) (k (j+1))) :
    let q := coeff ((a,δ)::w)
    ∀ j, denominator q.p q.r (2^q.d)*x j =
      numerator q.p q.r (2^q.d) (16*q.s) q.c q.e (q.d:Int) (2^(k j)) (k j:Int) := by
  let q := coeff ((a,δ)::w)
  have hp : q.p%2=0 := (coeff_nonempty_parity a δ w).1
  have hr : q.r%2=1 := coeff_r_odd _
  have hstep (j : Nat) := follows_affine (hf j)
  have hk (j : Nat) : (k (j+1):Int) = (k j:Int)+(q.d:Int) := by
    exact_mod_cast (hstep j).1
  have hz (j : Nat) : (2:Int)^(k (j+1)) = (2:Int)^q.d*2^(k j) := by
    rw [(hstep j).1,Int.pow_add]
    ac_rfl
  have hx (j : Nat) : q.p*x (j+1)=q.r*x j+(16*q.s)*2^(k j)+q.c*(k j:Int)+q.e := (hstep j).2
  exact affine_rigidity q.p q.r (2^q.d) (16*q.s) q.c q.e (q.d:Int)
    hp hr x (fun j => 2^(k j)) (fun j => (k j:Int)) hz hk hx

theorem repeated_word_divisibility (a δ : Nat) (w : List Token)
    (x : Nat → Int) (k : Nat → Nat)
    (hf : ∀ j, Follows ((a,δ)::w) (x j) (k j) (x (j+1)) (k (j+1))) :
    let q := coeff ((a,δ)::w)
    ∀ j, q.p*2^q.d-q.r ∣ (16*q.s)*2^(k j)*(2^q.d-1)^2 := by
  let q := coeff ((a,δ)::w)
  have hp : q.p%2=0 := (coeff_nonempty_parity a δ w).1
  have hr : q.r%2=1 := coeff_r_odd _
  have hstep (j : Nat) := follows_affine (hf j)
  have hk (j : Nat) : (k (j+1):Int) = (k j:Int)+(q.d:Int) := by
    exact_mod_cast (hstep j).1
  have hz (j : Nat) : (2:Int)^(k (j+1)) = (2:Int)^q.d*2^(k j) := by
    rw [(hstep j).1,Int.pow_add]
    ac_rfl
  have hx (j : Nat) : q.p*x (j+1)=q.r*x j+(16*q.s)*2^(k j)+q.c*(k j:Int)+q.e := (hstep j).2
  exact affine_exponential_divisibility q.p q.r (2^q.d) (16*q.s) q.c q.e (q.d:Int)
    hp hr x (fun j => 2^(k j)) (fun j => (k j:Int)) hz hk hx

#print axioms follows_affine
#print axioms coeff_nonempty_parity
#print axioms repeated_word_rigidity
#print axioms repeated_word_divisibility
end CascadePeriodic
