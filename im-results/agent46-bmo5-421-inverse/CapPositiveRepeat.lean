import CapPositiveGate

namespace CapSieve.Repeat

/-- A relaxed positive recurrence with absolute band index. -/
def Recurrence (s : Nat) (q : Nat → Int) (a : Nat → Nat) : Prop :=
  ∀ i, s≤i → 0<a i ∧ q (i+1)=(3:Int)^(a i)*q i-10*(2:Int)^i+3

theorem two_unit (n : Nat) : (2:Int)^n%3=1 ∨ (2:Int)^n%3=2 := by
  induction n with
  | zero => decide
  | succ n ih => rw [Int.pow_succ,Int.mul_emod]; rcases ih with h|h <;> rw [h] <;> decide

theorem recurrence_unit {s : Nat} {q : Nat → Int} {a : Nat → Nat}
    (h : Recurrence s q a) {i : Nat} (hi : s<i) : q i%3=(2:Int)^i%3 := by
  let k := i-1
  have hk : k+1=i := by dsimp [k]; omega
  obtain ⟨ha,he⟩ := h k (by dsimp [k]; omega)
  rw [←hk,Int.pow_succ]
  have hdiv : ((3:Int)^(a k)*q k)%3=0 := by
    cases hA : a k with
    | zero => omega
    | succ v => rw [Int.pow_succ,show (3:Int)^v*3*q k=3*((3:Int)^v*q k) by ac_rfl]; omega
  omega

theorem pow3_unit_rigid {u v : Nat} {x y : Int}
    (hx : x%3≠0) (hy : y%3≠0) (h : (3:Int)^u*x=(3:Int)^v*y) : u=v ∧ x=y := by
  induction u generalizing v with
  | zero =>
    cases v with
    | zero => simpa using h
    | succ v =>
      rw [Int.pow_zero,Int.one_mul,Int.pow_succ,show (3:Int)^v*3*y=3*((3:Int)^v*y) by ac_rfl] at h
      omega
  | succ u ih =>
    cases v with
    | zero =>
      rw [Int.pow_zero,Int.one_mul,Int.pow_succ,show (3:Int)^u*3*x=3*((3:Int)^u*x) by ac_rfl] at h
      omega
    | succ v =>
      rw [Int.pow_succ,Int.pow_succ,show (3:Int)^u*3*x=3*((3:Int)^u*x) by ac_rfl,
        show (3:Int)^v*3*y=3*((3:Int)^v*y) by ac_rfl] at h
      obtain ⟨h1,h2⟩ := ih (v:=v) (by omega)
      exact ⟨by omega,h2⟩

theorem unit_mul {x y : Int} (hx : x%3≠0) (hy : y%3≠0) : (x*y)%3≠0 := by
  rw [Int.mul_emod]
  have hx' : x%3=1 ∨ x%3=2 := by omega
  have hy' : y%3=1 ∨ y%3=2 := by omega
  rcases hx' with h|h <;> rcases hy' with g|g <;> rw [h,g] <;> decide

theorem pow2_mul_unit {n : Nat} {v : Int} (hv : v%3≠0) : ((2:Int)^n*v)%3≠0 :=
  unit_mul (by rcases two_unit n with h|h <;> omega) hv

/-- An affine periodic packet associated with an exponent word of length m. -/
structure Period (m : Nat) where
  a : Nat → Nat
  d : Nat → Int
  a_period : ∀ i, a (i+m)=a i
  d_period : ∀ i, d (i+m)=d i
  d_step : ∀ i, d (i+1)=(3:Int)^(a i)*d i-3*((2:Int)^m-1)
  d_unit : ∀ i, d i%3=0

def At {m : Nat} (p : Period m) (q : Nat → Int) (a : Nat → Nat) (k : Nat) : Prop :=
  q (k+m)=(2:Int)^m*q k+p.d k ∧ ∀ i, k≤i → i<k+m → a i=p.a i

/-- The backward packet equation is valid even at a nonunit seed. -/
theorem packet_equation {m s i : Nat} {p : Period m} {q : Nat → Int} {a : Nat → Nat}
    (hm : 0<m) (hr : Recurrence s q a) (hs : s≤i) (h : At p q a (i+1)) :
    a (i+m)=p.a i ∧
      (3:Int)^(a (i+m))*(q (i+m)-p.d i)=(2:Int)^m*((3:Int)^(a i)*q i) := by
  obtain ⟨hrel,hword⟩ := h
  have hmatch : a (i+m)=p.a i := (hword (i+m) (by omega) (by omega)).trans (p.a_period i)
  have e1 := (hr i hs).2
  have e2 := (hr (i+m) (by omega)).2
  rw [show i+m+1=i+1+m by omega,Int.pow_add] at e2
  have ed := p.d_step i
  rw [←hmatch] at ed
  have e3 : (3:Int)^(a (i+m))*q (i+m)=q (i+1+m)+10*((2:Int)^i*(2:Int)^m)-3 := by omega
  have e4 : (3:Int)^(a i)*q i=q (i+1)+10*(2:Int)^i-3 := by omega
  refine ⟨hmatch,?_⟩
  rw [Int.mul_sub,e3,hrel,ed,e4]
  simp only [Int.mul_add,Int.mul_sub,Int.mul_assoc]
  have he : (2:Int)^m*(10*(2:Int)^i)=10*((2:Int)^i*(2:Int)^m) := by ac_rfl
  have h3 : (2:Int)^m*3=3*(2:Int)^m := by ac_rfl
  rw [he,h3]
  omega

/-- An actual nonunit-free history forces the periodic packet backwards,
    because its exponent is the unique 3-adic valuation. -/
theorem packet_predecessor {m s i : Nat} {p : Period m} {q : Nat → Int} {a : Nat → Nat}
    (hm : 0<m) (hr : Recurrence s q a) (hs : s<i) (h : At p q a (i+1)) : At p q a i := by
  obtain ⟨hmch,he⟩ := packet_equation hm hr (by omega) h
  have hx : (q (i+m)-p.d i)%3≠0 := by
    have hu := recurrence_unit hr (show s<i+m by omega)
    have hp := two_unit (i+m)
    have hd := p.d_unit i
    omega
  have hy : ((2:Int)^m*q i)%3≠0 := by
    apply pow2_mul_unit
    have hu := recurrence_unit hr hs
    have hp := two_unit i
    omega
  rw [show (2:Int)^m*((3:Int)^(a i)*q i)=(3:Int)^(a i)*((2:Int)^m*q i) by ac_rfl] at he
  obtain ⟨ha,hq⟩ := pow3_unit_rigid hx hy he
  refine ⟨by omega,?_⟩
  intro j hj hj'
  by_cases hji : j=i
  · subst j; exact ha.symm.trans hmch
  · exact h.2 j (by omega) (by omega)

theorem packet_back {m s k : Nat} {p : Period m} {q : Nat → Int} {a : Nat → Nat}
    (hm : 0<m) (hr : Recurrence s q a) (hs : s+1≤k) (h : At p q a k) : At p q a (s+1) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases he : k=s+1
    · subst k; exact h
    · have hk : k-1+1=k := by omega
      have hp : At p q a (k-1+1) := by rw [hk]; exact h
      exact ih (k-1) (by omega) (by omega) (packet_predecessor hm hr (by omega) hp)

/-- The stripped seed unit and the extrapolated packet must have the same
    mod-3 phase. This is the root-sensitive obstruction. -/
theorem packet_seed_strip {m s r : Nat} {v : Int} {p : Period m} {q : Nat → Int} {a : Nat → Nat}
    (hm : 0<m) (hr : Recurrence s q a) (hseed : q s=(3:Int)^r*v)
    (hv : v%3≠0) (h : At p q a (s+1)) :
    q (s+m)=(2:Int)^m*v+p.d s ∧ v%3=(2:Int)^s%3 := by
  obtain ⟨hmch,he⟩ := packet_equation hm hr (by omega) h
  rw [hseed] at he
  have he' : (2:Int)^m*((3:Int)^(a s)*((3:Int)^r*v))=(3:Int)^(a s+r)*((2:Int)^m*v) := by
    rw [Int.pow_add]; ac_rfl
  rw [he'] at he
  have hx : (q (s+m)-p.d s)%3≠0 := by
    have hu := recurrence_unit hr (show s<s+m by omega)
    have hp := two_unit (s+m)
    have hd := p.d_unit s
    omega
  obtain ⟨_,hq⟩ := pow3_unit_rigid hx (pow2_mul_unit hv) he
  refine ⟨by omega,?_⟩
  have hqmod := congrArg (fun z : Int => z%3) hq
  have hd := p.d_unit s
  have hqm := recurrence_unit hr (show s<s+m by omega)
  have h1 : (q (s+m)-p.d s)%3=(2:Int)^(s+m)%3 := by omega
  rw [h1,Int.pow_add,Int.mul_emod,Int.mul_emod (a:=(2:Int)^m)] at hqmod
  have hm2 := two_unit m
  have hs2 := two_unit s
  have hv2 : v%3=1 ∨ v%3=2 := by omega
  rcases hm2 with hm2|hm2 <;> rcases hs2 with hs2|hs2 <;> rcases hv2 with hv2|hv2 <;> rw [hm2,hs2,hv2] at hqmod <;> omega

theorem no_packet_seed_six {m k : Nat} {p : Period m} {q : Nat → Int} {a : Nat → Nat}
    (hm : 0<m) (hr : Recurrence 0 q a) (hseed : q 0=6) (hk : 1≤k) (h : At p q a k) : False := by
  have h0 : q 0=(3:Int)^1*2 := by omega
  have hs := packet_seed_strip hm hr h0 (by decide) (packet_back hm hr hk h)
  exact (by decide : (2:Int)%3≠(2:Int)^0%3) hs.2

theorem no_packet_seed_eight {m k : Nat} {p : Period m} {q : Nat → Int} {a : Nat → Nat}
    (hm : 0<m) (hr : Recurrence 0 q a) (hseed : q 0=8) (hk : 1≤k) (h : At p q a k) : False := by
  have h0 : q 0=(3:Int)^0*8 := by omega
  have hs := packet_seed_strip hm hr h0 (by decide) (packet_back hm hr hk h)
  exact (by decide : (8:Int)%3≠(2:Int)^0%3) hs.2

/-- Difference equation for extrapolating a packet to smaller phase indices. -/
theorem packet_diff {m s i : Nat} {p : Period m} {q : Nat → Int} {a : Nat → Nat}
    (hr : Recurrence s q a) (hi : s≤i) (ha : a i=p.a i) :
    (3:Int)^(a i)*(q i-p.d i)=q (i+1)-p.d (i+1)+10*(2:Int)^i-3*(2:Int)^m := by
  have e1 := (hr i hi).2
  have e2 := p.d_step i
  rw [←ha] at e2
  rw [Int.mul_sub]
  omega

/-- Seed 15 at band one has the correct stripped unit, but its next three
    extrapolated backwards phases produce a contradiction. -/
theorem no_packet_seed_fifteen {m k : Nat} {p : Period m} {q : Nat → Int} {a : Nat → Nat}
    (hm : 4≤m) (hr : Recurrence 1 q a) (hseed : q 1=15) (hk : 2≤k) (h : At p q a k) : False := by
  have hb := packet_back (show 0<m by omega) hr hk h
  have h0 : q 1=(3:Int)^1*5 := by omega
  have hs := (packet_seed_strip (show 0<m by omega) hr h0 (by decide) hb).1
  have hnext : q (m+1)-p.d (m+1)=(2:Int)^m*5 := by
    rw [show m+1=1+m by omega,hs,p.d_period]
    omega
  have hu : ∀ i, 1<i → (q i-p.d i)%3≠0 := by
    intro i hi
    have hq := recurrence_unit hr hi
    have hp := two_unit i
    have hd := p.d_unit i
    omega
  have ha0 := hb.2 m (by omega) (by omega)
  have e0 := packet_diff hr (show 1≤m by omega) ha0
  rw [hnext] at e0
  have e0' : (3:Int)^(a m)*(q m-p.d m)=(3:Int)^1*((2:Int)^m*4) := by omega
  obtain ⟨_,h4⟩ := pow3_unit_rigid (hu m (by omega)) (pow2_mul_unit (n:=m) (by decide : (4:Int)%3≠0)) e0'
  have ha1 := hb.2 (m-1) (by omega) (by omega)
  have e1 := packet_diff hr (show 1≤m-1 by omega) ha1
  rw [show m-1+1=m by omega,h4] at e1
  have hP1 : (2:Int)^m=2*(2:Int)^(m-1) := by
    calc
      (2:Int)^m = (2:Int)^(m-1+1) := congrArg (fun n : Nat => (2:Int)^n) (by omega)
      _ = 2*(2:Int)^(m-1) := by rw [Int.pow_succ]; ac_rfl
  have e1' : (3:Int)^(a (m-1))*(q (m-1)-p.d (m-1))=(3:Int)^1*((2:Int)^m*2) := by omega
  obtain ⟨_,h2⟩ := pow3_unit_rigid (hu (m-1) (by omega)) (pow2_mul_unit (n:=m) (by decide : (2:Int)%3≠0)) e1'
  have ha2 := hb.2 (m-2) (by omega) (by omega)
  have e2 := packet_diff hr (show 1≤m-2 by omega) ha2
  rw [show m-2+1=m-1 by omega,h2] at e2
  have hP2 : (2:Int)^m=4*(2:Int)^(m-2) := by
    calc
      (2:Int)^m = (2:Int)^(m-2+2) := congrArg (fun n : Nat => (2:Int)^n) (by omega)
      _ = 4*(2:Int)^(m-2) := by rw [Int.pow_add]; simp; ac_rfl
  have e2' : (3:Int)^(a (m-2))*(q (m-2)-p.d (m-2))=(3:Int)^1*((2:Int)^(m-2)*2) := by omega
  obtain ⟨_,hbad⟩ := pow3_unit_rigid (hu (m-2) (by omega)) (pow2_mul_unit (n:=m-2) (by decide : (2:Int)%3≠0)) e2'
  have hq := recurrence_unit hr (show 1<m-2 by omega)
  have hd := p.d_unit (m-2)
  have hp := two_unit (m-2)
  omega

#print axioms no_packet_seed_six
#print axioms no_packet_seed_eight
#print axioms no_packet_seed_fifteen
end CapSieve.Repeat
