import SeamMass
namespace DyadicSeam
set_option maxHeartbeats 0

/-- The exact parity and dyadic valuation invariant before, at, and after
    disappearance of the seed's dyadic denominator. -/
def Shape (q p0 J p : Nat) : Prop :=
  (J=0 → p=p0) ∧
  (0<J → J<q → ∃ d, d%2=1 ∧ p0=p+2^(q-J)*d) ∧
  (J<q → p%2=1) ∧
  (J=q → p%2=0) ∧
  (q<J → p%2=1)

theorem pow2_even {n : Nat} (hn : 0<n) : 2^n%2=0 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  simp [Nat.pow_succ,Nat.mul_mod]

theorem pow3_odd (n : Nat) : 3^n%2=1 := by
  induction n with
  | zero => decide
  | succ n ih => simp [Nat.pow_succ,Nat.mul_mod,ih]

theorem seed_shape {q p0 : Nat} (hq : 0<q) (hp : p0%2=1) : Shape q p0 0 p0 := by
  unfold Shape
  exact ⟨fun _ => rfl,fun h => by omega,fun _ => hp,fun h => by omega,fun h => by omega⟩

theorem shape_step {q p0 A K J x y : Nat} (hKJ : K<J)
    (hs : Shape q p0 K x)
    (he : y+2^(q-J)*3^A=2^((J-q)-(K-q))*x) : Shape q p0 J y := by
  rcases hs with ⟨hzero,hbefore,hodd,hseam,hafter⟩
  refine ⟨fun h => by omega,?_,?_,?_,?_⟩
  · intro _ hJq
    have hKq : K<q := by omega
    have hshift : (J-q)-(K-q)=0 := by omega
    simp [hshift] at he
    by_cases hK : K=0
    · exact ⟨3^A,pow3_odd A,by rw [←hzero hK,←he]⟩
    · obtain ⟨d,hd,hp⟩ := hbefore (by omega) hKq
      have e : q-K=(q-J)+(J-K) := by omega
      rw [e,Nat.pow_add] at hp
      refine ⟨3^A+2^(J-K)*d,?_,?_⟩
      · simp [Nat.add_mod,Nat.mul_mod,pow3_odd,pow2_even (by omega : 0<J-K)]
      · rw [←he] at hp
        simpa [Nat.mul_add,Nat.mul_assoc,Nat.add_assoc] using hp
  · intro hJq
    have hKq : K<q := by omega
    have hshift : (J-q)-(K-q)=0 := by omega
    have h := congrArg (fun n : Nat => n%2) he
    simp [hshift,Nat.add_mod,Nat.mul_mod,pow2_even (by omega : 0<q-J),hodd hKq] at h
    omega
  · intro hJq
    have hKq : K<q := by omega
    have hshift : (J-q)-(K-q)=0 := by omega
    have hr : q-J=0 := by omega
    have h := congrArg (fun n : Nat => n%2) he
    simp [hshift,hr,Nat.add_mod,Nat.mul_mod,pow3_odd,hodd hKq] at h
    omega
  · intro hqJ
    have hshift : 0<(J-q)-(K-q) := by omega
    have hr : q-J=0 := by omega
    have h := congrArg (fun n : Nat => n%2) he
    simp [hr,Nat.add_mod,Nat.mul_mod,pow3_odd,pow2_even hshift] at h
    omega

theorem odd_pow_not_larger {a b x y : Nat} (hab : a<b) (hx : x%2=1)
    (he : 2^a*x=2^b*y) : False := by
  obtain ⟨d,hd⟩ : ∃ d,b=a+1+d := ⟨b-a-1,by omega⟩
  rw [hd,Nat.pow_add,Nat.pow_succ] at he
  have h : 2^a*x=2^a*(2*2^d*y) := by simpa [Nat.mul_assoc] using he
  have h' := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos a) h
  have hm := congrArg (fun n : Nat => n%2) h'
  simp [hx,Nat.mul_mod] at hm

theorem before_unique {q p0 K L p : Nat} (hK : K<q) (hL : L<q)
    (hs : Shape q p0 K p) (ht : Shape q p0 L p) : K=L := by
  by_cases h0 : K=0
  · by_cases h1 : L=0
    · omega
    · obtain ⟨d,hd,he⟩ := ht.2.1 (by omega) hL
      have hp := hs.1 h0
      have hpos : 0<2^(q-L)*d := Nat.mul_pos (Nat.two_pow_pos _) (by omega)
      omega
  · by_cases h1 : L=0
    · obtain ⟨d,hd,he⟩ := hs.2.1 (by omega) hK
      have hp := ht.1 h1
      have hpos : 0<2^(q-K)*d := Nat.mul_pos (Nat.two_pow_pos _) (by omega)
      omega
    · obtain ⟨d,hd,he⟩ := hs.2.1 (by omega) hK
      obtain ⟨e,he',hf⟩ := ht.2.1 (by omega) hL
      have eq : 2^(q-K)*d=2^(q-L)*e := by omega
      have hh := SeamMass.odd_pow_two_unique hd he' eq
      omega

/-- Fix the terminal exponent J. The normalized incoming product identifies
    the preceding cumulative exponent and numerator, including the crossing
    of the dyadic denominator. -/
theorem previous_unique {q p0 J K L x y : Nat} (hK : K<J) (hL : L<J)
    (hs : Shape q p0 K x) (ht : Shape q p0 L y)
    (he : 2^((J-q)-(K-q))*x=2^((J-q)-(L-q))*y) : K=L ∧ x=y := by
  by_cases hKq : K≤q
  · by_cases hLq : L≤q
    · have eK : K-q=0 := by omega
      have eL : L-q=0 := by omega
      rw [eK,eL] at he
      have hxy := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) he
      subst y
      refine ⟨?_,rfl⟩
      by_cases hKs : K=q
      · by_cases hLs : L=q
        · omega
        · have h1 := hs.2.2.2.1 hKs
          have h2 := ht.2.2.1 (by omega : L<q)
          omega
      · by_cases hLs : L=q
        · have h1 := hs.2.2.1 (by omega : K<q)
          have h2 := ht.2.2.2.1 hLs
          omega
        · exact before_unique (by omega) (by omega) hs ht
    · have e : (J-q)-(L-q)<(J-q)-(K-q) := by omega
      exact False.elim (odd_pow_not_larger e (ht.2.2.2.2 (by omega)) he.symm)
  · by_cases hLq : L≤q
    · have e : (J-q)-(K-q)<(J-q)-(L-q) := by omega
      exact False.elim (odd_pow_not_larger e (hs.2.2.2.2 (by omega)) he)
    · have e := SeamMass.odd_pow_two_unique (hs.2.2.2.2 (by omega)) (ht.2.2.2.2 (by omega)) he
      have eq : K=L := by omega
      subst L
      exact ⟨rfl,Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) he⟩

structure Node where
  J : Nat
  A : Nat
  p : Nat
  deriving DecidableEq

def root (p0 : Nat) : Node := ⟨0,0,p0⟩
def Band (q : Nat) (s : Node) : Prop :=
  2^(q-s.J)*3^s.A < 2*s.p ∧ s.p < 2^(q-s.J)*3^s.A

def Edge (q : Nat) (u v : Node) (j a : Nat) : Prop :=
  0<j ∧ v.J=u.J+j ∧ v.A=u.A+a ∧ Band q v ∧
  v.p+2^(q-v.J)*3^v.A=2^((v.J-q)-(u.J-q))*u.p ∧
  (0<u.J → SeamMass.Admissible j a)

/-- Words are stored terminal-to-seed, as in SeamMass.Path. -/
inductive Path (q p0 : Nat) : Node → List (Nat × Nat) → Prop
  | nil : Path q p0 (root p0) []
  | cons : Edge q u v j a → Path q p0 u w → Path q p0 v ((j,a)::w)

theorem path_shape {q p0 s w} (hq : 0<q) (hp : p0%2=1) (h : Path q p0 s w) :
    Shape q p0 s.J s.p := by
  induction h with
  | nil => exact seed_shape hq hp
  | cons he _ ih =>
    rcases he with ⟨hj,hJ,_,_,he,_⟩
    exact shape_step (by omega) ih he

theorem root_exponent {q p0 s w} (h : Path q p0 s w) (hJ : s.J=0) : s.A=0 := by
  cases h with
  | nil => rfl
  | cons he _ => have h1:=he.1; have h2:=he.2.1; omega

theorem edge_path_unique {q p0 : Nat} (hq : 0<q) (hp : p0%2=1)
    {u v s : Node} {j a k b : Nat} {w z : List (Nat × Nat)}
    (hu : Path q p0 u w) (hv : Path q p0 v z)
    (he : Edge q u s j a) (hf : Edge q v s k b) : u=v ∧ j=k ∧ a=b := by
  obtain ⟨hj,hJ,hA,_,heq,had⟩ := he
  obtain ⟨hk,hK,hB,_,heq',hbd⟩ := hf
  obtain ⟨hUV,hpp⟩ := previous_unique (by omega : u.J<s.J) (by omega : v.J<s.J)
    (path_shape hq hp hu) (path_shape hq hp hv) (heq.symm.trans heq')
  have hjk : j=k := by omega
  subst k
  have hab : a=b := by
    by_cases h : u.J=0
    · have h1 := root_exponent hu h
      have h2 := root_exponent hv (by omega)
      omega
    · exact SeamMass.exponent_unique (had (by omega)) (hbd (by omega))
  subst b
  have hAA : u.A=v.A := by omega
  have huv : u=v := by cases u; cases v; simp_all
  exact ⟨huv,rfl,rfl⟩

theorem path_unique {q p0 : Nat} (hq : 0<q) (hp : p0%2=1)
    {s : Node} {w z : List (Nat × Nat)} (hw : Path q p0 s w) (hz : Path q p0 s z) : w=z := by
  induction hw generalizing z with
  | nil =>
    cases hz with
    | nil => rfl
    | cons he _ => have h1:=he.1; have h2:=he.2.1; simp [root] at h2; omega
  | cons he hprev ih =>
    cases hz with
    | nil => have h1:=he.1; have h2:=he.2.1; simp [root] at h2; omega
    | cons hf hprev' =>
      obtain ⟨rfl,rfl,rfl⟩ := edge_path_unique hq hp hprev hprev' he hf
      rw [ih hprev']

#print axioms shape_step
#print axioms previous_unique
#print axioms path_unique
end DyadicSeam
