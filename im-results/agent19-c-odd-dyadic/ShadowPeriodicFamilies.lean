import Lean

namespace BB6.Agent19PeriodicFamilies

/-- Scaled version of the ordinary rational-shadow equations.
    The two equalities avoid any ambiguity from truncated natural subtraction. -/
def HighEdge (c d u v u' v' : Nat) : Prop :=
  let o := (u+v)%2
  2 ≤ d ∧ c*o ≤ u+v ∧
  2^d ∣ u+v-c*o ∧
  d%2=(u+1+o)%2 ∧
  2^(d-1)*u'=u+v-c*o+2^(d-1)*(c*(2+o)) ∧
  2*v'+u'=u+2*v+c*(3*d+1)

def DirectEdge (c u v u' v' : Nat) : Prop :=
  v%2=0 ∧ u'=u+v+2*c ∧ 2*v'=v+2*c

def Bad (u v : Nat) : Prop :=
  v%2=1 ∧ ((u+v)%4=1 ∨ (u+v)%4=2)

/-- A prime denominator already permits an infinite non-leaf path. -/
theorem prime_seven_path (k : Nat) :
    HighEdge 7 3 (16+10*k) (32+30*k) (16+10*(k+1)) (32+30*(k+1)) ∧
    14<16+10*k ∧ 14<32+30*k ∧ ¬Bad (16+10*k) (32+30*k) := by
  unfold HighEdge Bad
  have hmod : (16+10*k+(32+30*k))%2=0 := by omega
  rw [hmod]
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.add_zero]
  refine ⟨⟨by decide,by omega,⟨6+5*k,by omega⟩,by omega,by omega,by omega⟩,
    by omega,by omega,by omega⟩

/-- A period containing a direct edge and a high edge. -/
theorem fifteen_alternating_path (k : Nat) :
    DirectEdge 15 (31+42*k) (34+84*k) (95+126*k) (32+42*k) ∧
    HighEdge 15 3 (95+126*k) (32+42*k) (31+42*(k+1)) (34+84*(k+1)) ∧
    30<31+42*k ∧ 30<34+84*k ∧ 30<95+126*k ∧ 30<32+42*k ∧
    ¬Bad (31+42*k) (34+84*k) ∧ ¬Bad (95+126*k) (32+42*k) := by
  unfold DirectEdge HighEdge Bad
  have hmod : (95+126*k+(32+42*k))%2=1 := by omega
  rw [hmod]
  simp only [Nat.mul_one]
  refine ⟨⟨by omega,by omega,by omega⟩,
    ⟨by decide,by omega,⟨14+21*k,by omega⟩,by omega,by omega,by omega⟩,
    by omega,by omega,by omega,by omega,by omega,by omega⟩

#print axioms prime_seven_path
#print axioms fifteen_alternating_path

/-- An integer error which is divided by a fixed factor at every step
    is identically zero along an infinite sequence. -/
theorem integer_decay (D : Int) (hD : 2≤D) (e : Nat→Int)
    (he : ∀ k, D*e (k+1)=e k) : ∀ k, e k=0 := by
  have hmono : ∀ k, e k≠0 → e (k+1)≠0 ∧ (e (k+1)).natAbs<(e k).natAbs := by
    intro k hn
    have hn' : e (k+1)≠0 := by
      intro hz
      have h := he k
      rw [hz,Int.mul_zero] at h
      exact hn h.symm
    refine ⟨hn',?_⟩
    have hAbs := congrArg Int.natAbs (he k)
    rw [Int.natAbs_mul] at hAbs
    have hDp : 2≤D.natAbs := by omega
    have hEn : 0<(e (k+1)).natAbs := by omega
    have hMul : 2*(e (k+1)).natAbs≤D.natAbs*(e (k+1)).natAbs :=
      Nat.mul_le_mul_right _ hDp
    omega
  intro k
  by_cases h : e k=0
  · exact h
  · have hbound : ∀ n, e (k+n)≠0 ∧ (e (k+n)).natAbs+n≤(e k).natAbs := by
      intro n
      induction n with
      | zero => simpa using h
      | succ n ih =>
        obtain ⟨hn,hlt⟩:=hmono (k+n) ih.1
        rw [←Nat.add_assoc]
        exact ⟨hn,by omega⟩
    have := (hbound ((e k).natAbs+1)).2
    omega

/-- Exact drift forced by an infinite affine constant-cost recurrence. -/
theorem constant_affine_drift (D W B : Int) (hD : 2≤D)
    (U S : Nat→Int)
    (hu : ∀ k, D*U (k+1)=U k+S k+B)
    (hs : ∀ k, S (k+1)=S k+W) :
    ∀ k, (D-1)*(U (k+1)-U k)=W := by
  let q := D-1
  let e := fun k : Nat => q*q*U k-q*(S k+B)+D*W
  have he : ∀ k, D*e (k+1)=e k := by
    intro k
    have hU := hu k
    have hS := hs k
    dsimp [e,q]
    grind
  have hz := integer_decay D hD e he
  intro k
  have h0 := hz k
  have h1 := hz (k+1)
  have hS := hs k
  have hq : q≠0 := by omega
  have hprod : q*(q*(U (k+1)-U k)-W)=0 := by
    dsimp [e] at h0 h1
    grind
  have hzero := (Int.mul_eq_zero.mp hprod).resolve_left hq
  have heq : q*(U (k+1)-U k)=W := by omega
  simpa [q] using heq

#print axioms integer_decay
#print axioms constant_affine_drift

theorem constant_odd_necessary (c d : Nat) (hd : 3≤d) (ho : d%2=1)
    (u v : Nat→Nat)
    (edge : ∀ k, HighEdge c d (u k) (v k) (u (k+1)) (v (k+1))) :
    (2^d-1) ∣ c*((3*d+1)/2) := by
  let s := fun k => u k+2*v k
  let o := u 0%2
  have hS : ∀ k, s (k+1)=s k+c*(3*d+1) := by
    intro k
    have he := (edge k)
    unfold HighEdge at he
    dsimp [s]
    omega
  have hW : (c*(3*d+1))%2=0 := by
    rw [Nat.mul_mod]
    have hz : (3*d+1)%2=0 := by omega
    simp [hz]
  have hU : ∀ k, u k%2=o := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      have h := hS k
      dsimp [s] at h
      omega
  have hV : ∀ k, v k%2=0 := by
    intro k
    have he := edge k
    unfold HighEdge at he
    omega
  have hO : ∀ k, (u k+v k)%2=o := by
    intro k
    have hu := hU k
    have hv := hV k
    omega
  let D : Int := (2^d:Nat)
  let W : Int := (c*(3*d+1):Nat)
  let B : Int := D*(c*(2+o):Nat)-2*(c*o:Nat)
  have hpow : 2^d=2^(d-1)*2 := by
    calc
      2^d = 2^((d-1)+1) := by congr 1; omega
      _ = _ := Nat.pow_succ ..
  have hDnat : 2≤(2:Nat)^d := by
    exact Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega : 1≤d)
  have hD : 2≤D := by omega
  have hstep : ∀ k, D*(u (k+1):Int)=(u k:Int)+(s k:Int)+B := by
    intro k
    have he := edge k
    unfold HighEdge at he
    rw [hO k] at he
    have hsub := Nat.sub_add_cancel he.2.1
    have hEq := he.2.2.2.2.1
    have hNat : 2^d*u (k+1)+2*(c*o)=u k+s k+2^d*(c*(2+o)) := by
      rw [hpow]
      dsimp [s]
      grind
    have hInt := congrArg (fun n : Nat => (n:Int)) hNat
    push_cast at hInt
    dsimp [D,B]
    omega
  have hSm : ∀ k, (s (k+1):Int)=(s k:Int)+W := by
    intro k
    have h := congrArg (fun n : Nat => (n:Int)) (hS k)
    dsimp [W]
    push_cast at h ⊢
    exact h
  have hdrift := constant_affine_drift D W B hD
    (fun k => (u k:Int)) (fun k => (s k:Int)) hstep hSm 0
  have hq : ((2^d-1:Nat):Int)=D-1 := by
    dsimp [D]
    rw [Int.ofNat_sub (by omega)]
    rfl
  have hDiv : ((2^d-1:Nat):Int) ∣ ((c*(3*d+1):Nat):Int) := by
    refine ⟨(u 1:Int)-(u 0:Int),?_⟩
    rw [hq]
    exact hdrift.symm
  have hdivNat := Int.ofNat_dvd.mp hDiv
  obtain ⟨k,hk⟩ := hdivNat
  have hqodd : (2^d-1)%2=1 := by
    have he : (2^d)%2=0 := by
      rw [hpow]
      simp
    omega
  have hke : k%2=0 := by
    have h := congrArg (fun x : Nat => x%2) hk
    rw [Nat.mul_mod (2^d-1),hqodd] at h
    simp only [Nat.one_mul,Nat.mod_mod] at h
    omega
  refine ⟨k/2,?_⟩
  have hhalf : 2*((3*d+1)/2)=3*d+1 := by omega
  have hkhalf : 2*(k/2)=k := by omega
  have he : 2*(c*((3*d+1)/2))=2*((2^d-1)*(k/2)) := by
    rw [Nat.mul_left_comm 2 c,hhalf,Nat.mul_left_comm 2 (2^d-1),hkhalf]
    exact hk
  omega

#print axioms constant_odd_necessary

def genU (c delta k : Nat) := 6*c+2*delta*k
def genV (a c delta k : Nat) := 2*((a+1)*delta*k+(2*a+1)*c+(a+2)*delta)

theorem constant_odd_sufficient (c d : Nat) (hc : 0<c) (hd : 3≤d) (ho : d%2=1)
    (hdiv : (2^d-1) ∣ c*((3*d+1)/2)) :
    ∃ u v : Nat→Nat, ∀ k,
      2*c<u k ∧ 2*c<v k ∧ ¬Bad (u k) (v k) ∧
      HighEdge c d (u k) (v k) (u (k+1)) (v (k+1)) := by
  obtain ⟨delta,hdelta⟩ := hdiv
  let a := 2^(d-1)-2
  have hp : 4≤2^(d-1) :=
    Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega : 2≤d-1)
  have ha : 2^(d-1)=a+2 := by omega
  have ha2 : 2≤a := by omega
  have hpow : 2^d=2*(a+2) := by
    calc
      2^d = 2^((d-1)+1) := by congr 1; omega
      _ = _ := Nat.pow_succ ..
      _ = _ := by rw [ha,Nat.mul_comm]
  have hq : 2^d-1=2*a+3 := by omega
  rw [hq] at hdelta
  have hhalf : 2*((3*d+1)/2)=3*d+1 := by omega
  have hmassShift : c*(3*d+1)=2*((2*a+3)*delta) := by
    rw [←hdelta,←Nat.mul_left_comm,hhalf]
  refine ⟨genU c delta,genV a c delta,?_⟩
  intro k
  have hm : genU c delta k+genV a c delta k=2*(a+2)*(2*c+delta*(k+1)) := by
    simp only [genU,genV,Nat.mul_add,Nat.add_mul]
    grind
  have hu : genU c delta (k+1)=genU c delta k+2*delta := by
    simp [genU,Nat.mul_add,Nat.add_assoc]
  have hv : genV a c delta (k+1)=genV a c delta k+2*((a+1)*delta) := by
    simp only [genV,Nat.mul_add]
    omega
  have hUeven : genU c delta k%2=0 := by
    unfold genU
    rw [show 6*c=2*(3*c) by omega, Nat.mul_assoc,←Nat.mul_add]
    simp
  have hVeven : genV a c delta k%2=0 := by simp [genV]
  refine ⟨?_,?_,by simp [Bad,hVeven],?_⟩
  · unfold genU
    omega
  · have h := Nat.mul_le_mul_right c (show 3≤2*a+1 by omega)
    unfold genV
    omega
  · unfold HighEdge
    rw [show (genU c delta k+genV a c delta k)%2=0 by omega]
    simp only [Nat.mul_zero,Nat.sub_zero,Nat.add_zero]
    refine ⟨by omega,by omega,⟨2*c+delta*(k+1),by rw [hm,hpow]⟩,by omega,?_,?_⟩
    · rw [ha,hm]
      simp only [genU,Nat.mul_add,Nat.add_mul]
      grind
    · rw [hu,hv,hmassShift]
      simp only [Nat.mul_add,Nat.add_mul]
      grind

/-- Complete existence criterion for a positive non-leaf constant
    odd-cost path, for every positive denominator. -/
theorem constant_odd_iff (c d : Nat) (hc : 0<c) (hd : 3≤d) (ho : d%2=1) :
    (∃ u v : Nat→Nat, ∀ k,
      2*c<u k ∧ 2*c<v k ∧ ¬Bad (u k) (v k) ∧
      HighEdge c d (u k) (v k) (u (k+1)) (v (k+1))) ↔
    (2^d-1) ∣ c*((3*d+1)/2) := by
  constructor
  · rintro ⟨u,v,h⟩
    exact constant_odd_necessary c d hd ho u v (fun k => (h k).2.2.2)
  · exact constant_odd_sufficient c d hc hd ho

#print axioms constant_odd_sufficient
#print axioms constant_odd_iff

end BB6.Agent19PeriodicFamilies
