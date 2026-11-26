import Std
namespace SeamMass

def Admissible (j a : Nat) : Prop :=
  2^j < 4*3^a ∧ 3*3^a < 2^(j+1)

theorem three_pow_gap {a b : Nat} (h : a < b) : 3*3^a ≤ 3^b := by
  have hp : 3^(a+1) ≤ 3^b := Nat.pow_le_pow_right (by decide) h
  simpa [Nat.pow_succ, Nat.mul_comm] using hp

theorem exponent_unique {j a b : Nat} (ha : Admissible j a) (hb : Admissible j b) : a=b := by
  rcases ha with ⟨ha1,ha2⟩
  rcases hb with ⟨hb1,hb2⟩
  rw [Nat.pow_succ] at ha2 hb2
  rcases Nat.lt_trichotomy a b with h|h|h
  · have := three_pow_gap h
    omega
  · exact h
  · have := three_pow_gap h
    omega

theorem exponent_two_forbidden (a : Nat) : ¬ Admissible 2 a := by
  intro ⟨hl,hu⟩
  cases a with
  | zero => simp at hl
  | succ a =>
    have h := Nat.one_le_pow a 3 (by decide)
    rw [Nat.pow_succ] at hu
    omega

theorem exponent_zero_forbidden (a : Nat) : ¬ Admissible 0 a := by
  intro ⟨_,hu⟩
  have h := Nat.one_le_pow a 3 (by decide)
  omega

theorem exponent_one_zero {a : Nat} (h : Admissible 1 a) : a=0 :=
  exponent_unique h (by unfold Admissible; decide)

theorem odd_pow_two_unique {j k p q : Nat} (hp : p%2=1) (hq : q%2=1)
    (he : 2^j*p=2^k*q) : j=k := by
  rcases Nat.lt_trichotomy j k with h|h|h
  · obtain ⟨d,hd⟩ : ∃d, k=j+1+d := ⟨k-j-1, by omega⟩
    rw [hd,Nat.pow_add,Nat.pow_succ] at he
    have he' : 2^j*p=2^j*(2*2^d*q) := by
      simpa [Nat.mul_assoc] using he
    have hpos : 0 < 2^j := Nat.two_pow_pos j
    have he'' := Nat.eq_of_mul_eq_mul_left hpos he'
    have hm := congrArg (fun n : Nat => n%2) he''
    simp [hp,Nat.mul_mod] at hm
  · exact h
  · obtain ⟨d,hd⟩ : ∃d, j=k+1+d := ⟨j-k-1, by omega⟩
    rw [hd,Nat.pow_add,Nat.pow_succ] at he
    have he' : 2^k*(2*2^d*p)=2^k*q := by
      simpa [Nat.mul_assoc] using he
    have hpos : 0 < 2^k := Nat.two_pow_pos k
    have he'' := Nat.eq_of_mul_eq_mul_left hpos he'
    have hm := congrArg (fun n : Nat => n%2) he''
    simp [hq,Nat.mul_mod] at hm

structure State where
  A : Nat
  p : Nat
  deriving DecidableEq

def Valid (s : State) : Prop :=
  3^s.A < 2*s.p ∧ s.p ≤ 3^s.A ∧ s.p%2=1

def Edge (s t : State) (j a : Nat) : Prop :=
  Valid s ∧ Valid t ∧ s.A=t.A+a ∧ s.p+3^s.A=2^j*t.p ∧ Admissible j a

theorem admissible_of_band {s t : State} {j a : Nat}
    (hs : Valid s) (ht : Valid t) (hstrict : s.p < 3^s.A)
    (hA : s.A=t.A+a) (hp : s.p+3^s.A=2^j*t.p) : Admissible j a := by
  rcases hs with ⟨hsl,_,_⟩
  rcases ht with ⟨htl,htu,_⟩
  have hd : 3^s.A=3^t.A*3^a := by rw [hA,Nat.pow_add]
  rw [hd] at hsl hstrict hp
  constructor
  · apply Nat.lt_of_mul_lt_mul_right (a:=3^t.A)
    have h1 := Nat.mul_lt_mul_of_pos_left htl (Nat.two_pow_pos j)
    have h2 : 2^j*(2*t.p)=2*(s.p+3^t.A*3^a) := by rw [hp]; ac_rfl
    rw [h2] at h1
    have h3 : 4*3^a*3^t.A=4*(3^t.A*3^a) := by ac_rfl
    rw [h3]
    omega
  · apply Nat.lt_of_mul_lt_mul_right (a:=3^t.A)
    have h1 := Nat.mul_le_mul_left (2^(j+1)) htu
    have h2 : 2^(j+1)*t.p=2*(s.p+3^t.A*3^a) := by
      rw [Nat.pow_succ,show (2^j*2)*t.p=2*(2^j*t.p) by ac_rfl,←hp]
    rw [h2] at h1
    have h3 : 3*3^a*3^t.A=3*(3^t.A*3^a) := by ac_rfl
    rw [h3]
    omega

theorem edge_unique {s t u : State} {j k a b : Nat}
    (h : Edge s t j a) (g : Edge s u k b) : t=u ∧ j=k ∧ a=b := by
  rcases h with ⟨_,⟨_,_,ht⟩,hA,hp,hj⟩
  rcases g with ⟨_,⟨_,_,hu⟩,gA,gp,gk⟩
  have he : 2^j*t.p=2^k*u.p := hp.symm.trans gp
  have h := odd_pow_two_unique ht hu he
  subst k
  have hab := exponent_unique hj gk
  subst b
  have hpp := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos j) he
  have hAA : t.A=u.A := by omega
  cases t; cases u; simp_all

def root : State := ⟨0,1⟩
inductive Path : State → List (Nat × Nat) → Prop
  | nil : Path root []
  | cons : Edge s t j a → 0 < s.A → Path t w → Path s ((j,a)::w)

theorem path_unique {s : State} {w v : List (Nat × Nat)}
    (h : Path s w) (g : Path s v) : w=v := by
  induction h generalizing v with
  | nil =>
    cases g with
    | nil => rfl
    | cons _ hA _ => simp [root] at hA
  | cons he hA hp ih =>
    cases g with
    | nil => simp [root] at hA
    | cons ge _ gp =>
      obtain ⟨rfl,rfl,rfl⟩ := edge_unique he ge
      rw [ih gp]

def totalJ (w : List (Nat × Nat)) : Nat := (w.map Prod.fst).sum

theorem path_budget {s : State} {w : List (Nat × Nat)}
    (h : Path s w) : s.p ≤ 2^totalJ w ∧ (0<s.A → 3^s.A < 2^totalJ w) := by
  induction h with
  | nil => simp [root,totalJ]
  | @cons s t j a w he hA hp ih =>
    obtain ⟨hs,_,_,eq,_⟩ := he
    have hle := Nat.mul_le_mul_left (2^j) ih.1
    have hle' : s.p+3^s.A ≤ 2^j*2^totalJ w := by rw [eq]; exact hle
    have hspos : 0<s.p := by
      have := hs.1
      omega
    simp only [totalJ,List.map_cons,List.sum_cons,Nat.pow_add]
    change s.p ≤ 2^j*2^totalJ w ∧ (0<s.A → 3^s.A < 2^j*2^totalJ w)
    exact ⟨Nat.le_trans (Nat.le_add_right _ _) hle',fun _ => by omega⟩

/-- Counts of length-n binary continuations from the three automaton states:
    boundary, exactly one zero, at least two zeros. A one after exactly one
    zero is forbidden (the missing valuation j=2). -/
def prefixCounts : Nat → Nat × Nat × Nat
  | 0 => (1,1,1)
  | n+1 => let (x,y,z) := prefixCounts n; (x+y,z,z+x)

theorem prefix_majorant (n : Nat) :
    7*9^n*(prefixCounts n).1 ≤ 9*16^n ∧
    7*9^n*(prefixCounts n).2.1 ≤ 7*16^n ∧
    7*9^n*(prefixCounts n).2.2 ≤ 12*16^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rcases h : prefixCounts n with ⟨x,y,z⟩
    rw [h] at ih
    change 7*9^n*x ≤ 9*16^n ∧ 7*9^n*y ≤ 7*16^n ∧ 7*9^n*z ≤ 12*16^n at ih
    rcases ih with ⟨hx,hy,hz⟩
    simp only [prefixCounts,h,Nat.pow_succ]
    have e (k : Nat) : 7*(9^n*9)*k=9*(7*9^n*k) := by ac_rfl
    simp only [e,Nat.mul_add]
    have e1 : 9*(16^n*16)=144*16^n := by rw [Nat.mul_comm (16^n) 16,←Nat.mul_assoc]
    have e2 : 7*(16^n*16)=112*16^n := by rw [Nat.mul_comm (16^n) 16,←Nat.mul_assoc]
    have e3 : 12*(16^n*16)=192*16^n := by rw [Nat.mul_comm (16^n) 16,←Nat.mul_assoc]
    rw [e1,e2,e3]
    omega

#print axioms exponent_unique
#print axioms exponent_two_forbidden
#print axioms admissible_of_band
#print axioms edge_unique
#print axioms path_unique
#print axioms path_budget
#print axioms prefix_majorant
end SeamMass
