import Lean

namespace BB6.Agent19Scalar

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

-- Exact ordinary grammar (same equations as ShadowPeriodicFamilies).
def HighEdge (c d u v u' v' : Nat) : Prop :=
  let o := (u+v)%2
  2 ≤ d ∧ c*o ≤ u+v ∧
  2^d ∣ u+v-c*o ∧
  d%2=(u+1+o)%2 ∧
  2^(d-1)*u'=u+v-c*o+2^(d-1)*(c*(2+o)) ∧
  2*v'+u'=u+2*v+c*(3*d+1)

def DirectEdge (c u v u' v' : Nat) : Prop :=
  v%2=0 ∧ u'=u+v+2*c ∧ 2*v'=v+2*c

def Ordinary (d u v u' v' : Nat) : Prop :=
  (d=1 ∧ DirectEdge 211 u v u' v') ∨ HighEdge 211 d u v u' v'

def Bad (u v : Nat) : Prop :=
  v%2=1 ∧ ((u+v)%4=1 ∨ (u+v)%4=2)

def s (m : Nat) := (m+1)%2
def base (m : Nat) := 211*(m/2)+108
def U (m x : Nat) := 2*x+211*(2+s m)
def V (m x : Nat) := base m-(x+211*(1+s m))
def Good (m x : Nat) : Prop := 0<x ∧ x+211*(1+s m)+422<base m
def A (m x : Nat) := x+base m
def Q (m x : Nat) := A m x+211*(A m x%2)

/-- All ordinary edges become a single scalar quotient rule. -/
def Step (m x d m' x' : Nat) : Prop :=
  0<d ∧ m'=m+3*d+1 ∧ m'%2=A m x%2 ∧ 2^d*x'=Q m x

private theorem mass (m x : Nat) (h : Good m x) : U m x+2*V m x=5+211*m := by
  unfold Good U V base s at *
  omega

private theorem parity (m x : Nat) (h : Good m x) :
    U m x%2=s m ∧ (U m x+V m x)%2=1-A m x%2 ∧
    Q m x=U m x+V m x-211*((U m x+V m x)%2) := by
  simp only [Good,U,V,base,s,A,Q] at *
  omega

private theorem pow_split (d : Nat) (hd : 0<d) : (2:Nat)^d=2^(d-1)*2 := by
  calc
    2^d = 2^((d-1)+1) := by congr 1; omega
    _ = _ := Nat.pow_succ ..

/-- Scalar edges preserve the positive domain. -/
theorem step_good {m x d m' x' : Nat} (h : Good m x)
    (he : Step m x d m' x') : Good m' x' := by
  obtain ⟨hd,hm,hp,heq⟩ := he
  have hqpos : 0<Q m x := by unfold Q A base; omega
  have hx : 0<x' := by
    by_cases hz : x'=0
    · rw [hz,Nat.mul_zero] at heq
      omega
    · omega
  refine ⟨hx,?_⟩
  by_cases h1 : d=1
  · subst d
    change 2*x'=Q m x at heq
    simp only [Good,base,s,Q,A] at *
    omega
  · have hd2 : 2≤d := by omega
    have hpow : 4≤(2:Nat)^d := by
      simpa using Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hd2
    have h4 : 4*x'≤Q m x := by rw [←heq]; exact Nat.mul_le_mul_right _ hpow
    simp only [Good,base,s,Q,A] at *
    omega

private theorem scalar_iff_aux (m d m' x' u v u' v' a q : Nat)
    (hm : u+2*v=5+211*m) (hm' : u'+2*v'=5+211*m')
    (hu : u%2=(m+1)%2) (hu' : u'%2=(m'+1)%2)
    (ho : (u+v)%2=1-a%2) (hq : q=u+v-211*((u+v)%2))
    (hpos : 211*((u+v)%2)≤u+v)
    (hU' : u'=2*x'+211*(2+(m'+1)%2)) :
    (0<d ∧ m'=m+3*d+1 ∧ m'%2=a%2 ∧ 2^d*x'=q) ↔ Ordinary d u v u' v' := by
  constructor
  · rintro ⟨hd,hM,hP,hE⟩
    have hso : (m'+1)%2=(u+v)%2 := by omega
    have hpar : d%2=(u+1+(u+v)%2)%2 := by omega
    have hmass : u'+2*v'=u+2*v+211*(3*d+1) := by omega
    by_cases h1 : d=1
    · subst d
      left
      refine ⟨rfl,?_⟩
      unfold DirectEdge
      have hve : v%2=0 := by omega
      change 2*x'=q at hE
      exact ⟨hve,by omega,by omega⟩
    · right
      unfold HighEdge
      refine ⟨by omega,hpos,⟨x',by omega⟩,hpar,?_,by omega⟩
      rw [hU',hso,Nat.mul_add,←Nat.mul_assoc,←pow_split d hd,hE,hq]
  · intro hE
    rcases hE with ⟨h1,hD⟩ | hH
    · subst d
      unfold DirectEdge at hD
      obtain ⟨hv,hU,hV⟩ := hD
      have hM : m'=m+4 := by
        clear hu hu' ho hq hpos hU' hv
        omega
      have hso : (m'+1)%2=(u+v)%2 := by
        clear hm hm' hu' ho hq hpos hU' hU hV
        omega
      refine ⟨by decide,by simpa using hM,?_,?_⟩
      · clear hm hm' hu hu' hq hpos hU' hv hU hV hM
        omega
      · change 2*x'=q
        clear hm hm' hu hu' ho hv hV hM
        omega
    · unfold HighEdge at hH
      obtain ⟨hd,_,_,hpar,hEq,hMass⟩ := hH
      have hM : m'=m+3*d+1 := by
        clear hu hu' ho hq hpos hU' hd hpar hEq
        omega
      have hso : (m'+1)%2=(u+v)%2 := by
        clear hm hm' hu' ho hq hpos hU' hEq hMass hd
        omega
      refine ⟨by omega,hM,?_,?_⟩
      · clear hm hm' hu hu' hq hpos hU' hpar hEq hMass hM hd
        omega
      · rw [hU',hso,Nat.mul_add,←Nat.mul_assoc,←pow_split d (by omega)] at hEq
        clear hm hm' hu hu' ho hpos hU' hpar hMass hM hso
        omega

/-- Positive scalar states are exactly the corresponding ordinary shadows. -/
theorem scalar_iff {m x d m' x' : Nat} (h : Good m x) (h' : Good m' x') :
    Step m x d m' x' ↔ Ordinary d (U m x) (V m x) (U m' x') (V m' x') := by
  have hm := mass m x h
  have hm' := mass m' x' h'
  obtain ⟨hu,ho,hq⟩ := parity m x h
  obtain ⟨hu',_,_⟩ := parity m' x' h'
  have hpos : 211*((U m x+V m x)%2)≤U m x+V m x := by
    have hv : 422<V m x := by unfold Good V at *; omega
    omega
  exact scalar_iff_aux m d m' x' (U m x) (V m x) (U m' x') (V m' x')
    (A m x) (Q m x) hm hm' hu hu' ho hq hpos rfl

/-- Every sufficiently positive normalized shadow has the scalar coordinates. -/
theorem decode_exists (u v : Nat) (hu : 211*(2+u%2)<u) (hv : 422<v)
    (hm : (u+2*v)%211=5) : ∃ m x, Good m x ∧ U m x=u ∧ V m x=v := by
  let m := (u+2*v)/211
  let x := (u-211*(2+u%2))/2
  have hMass : u+2*v=5+211*m := by dsimp [m]; omega
  have hs : s m=u%2 := by unfold s; omega
  have hX : 2*x+211*(2+u%2)=u := by dsimp [x]; omega
  have hY : 2*base m=5+211*m+211*s m := by unfold base s; omega
  refine ⟨m,x,⟨by omega,by omega⟩,?_,?_⟩
  · unfold U
    rw [hs,hX]
  · unfold V
    omega

/-- The child determines its entire incoming edge: the ordinary positive
    shadow graph is a forest (edges are oriented toward increasing mass). -/
theorem incoming_unique {m₁ x₁ d₁ m₂ x₂ d₂ m' x' : Nat}
    (g₁ : Good m₁ x₁) (g₂ : Good m₂ x₂)
    (e₁ : Step m₁ x₁ d₁ m' x') (e₂ : Step m₂ x₂ d₂ m' x') :
    m₁=m₂ ∧ x₁=x₂ ∧ d₁=d₂ := by
  obtain ⟨hd₁,hm₁,hp₁,hq₁⟩ := e₁
  obtain ⟨hd₂,hm₂,hp₂,hq₂⟩ := e₂
  have hq₁' : 2^d₁*x'=x₁+base m₁+211*(m'%2) := by rw [hq₁]; unfold Q; rw [←hp₁]; rfl
  have hq₂' : 2^d₂*x'=x₂+base m₂+211*(m'%2) := by rw [hq₂]; unfold Q; rw [←hp₂]; rfl
  have notlt : ∀ a b p q d e : Nat, Good a p → Good b q →
      m'=a+3*d+1 → m'=b+3*e+1 →
      2^d*x'=p+base a+211*(m'%2) → 2^e*x'=q+base b+211*(m'%2) → ¬d<e := by
    intro a b p q d e ga gb ha hb he₁ he₂ hlt
    have hbase : base b≤base a := by unfold base; omega
    have hp : 2^d*2≤(2:Nat)^e := by
      rw [←Nat.pow_succ]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have hmul := Nat.mul_le_mul_right x' hp
    rw [Nat.mul_right_comm (2^d) 2 x',he₁,he₂] at hmul
    unfold Good at ga gb
    omega
  have hde : d₁=d₂ := by
    have h₁ := notlt m₁ m₂ x₁ x₂ d₁ d₂ g₁ g₂ hm₁ hm₂ hq₁' hq₂'
    have h₂ := notlt m₂ m₁ x₂ x₁ d₂ d₁ g₂ g₁ hm₂ hm₁ hq₂' hq₁'
    omega
  have hme : m₁=m₂ := by omega
  rw [hde,hme] at hq₁'
  exact ⟨hme,by omega,hde⟩

/-- Bad is exactly the absence of any legal scalar child. -/
theorem child_iff_not_bad {m x : Nat} (g : Good m x) :
    (∃ d m' x', Step m x d m' x') ↔ ¬Bad (U m x) (V m x) := by
  obtain ⟨hu,ho,hq⟩ := parity m x g
  have hQeven : Q m x%2=0 := by unfold Q; omega
  have hbad : Bad (U m x) (V m x) ↔ V m x%2=1 ∧ Q m x%4=2 := by
    have hpos : 422<V m x := by unfold Good V at *; omega
    unfold Bad
    omega
  have hpar : V m x%2=(m+A m x)%2 := by unfold s at hu; omega
  constructor
  · rintro ⟨d,m',x',hd,hm,hp,he⟩
    rw [hbad]
    rintro ⟨hv,hmod⟩
    have hd2 : 2≤d := by omega
    have hdiv : (4:Nat)∣2^d := Nat.pow_dvd_pow 2 hd2
    have hdiv' : 4∣Q m x := by
      rw [←he]
      exact Nat.dvd_trans hdiv (Nat.dvd_mul_right _ _)
    have := Nat.mod_eq_zero_of_dvd hdiv'
    omega
  · intro h
    rw [hbad] at h
    by_cases hv : V m x%2=0
    · refine ⟨1,m+4,Q m x/2,by decide,by omega,by omega,?_⟩
      change 2*(Q m x/2)=Q m x
      omega
    · have hQ4 : Q m x%4=0 := by omega
      refine ⟨2,m+7,Q m x/4,by decide,by omega,by omega,?_⟩
      change 4*(Q m x/4)=Q m x
      omega

/-- All siblings share exactly the same exponential-weighted cube. -/
theorem sibling_mass_cube {m x d m' x' : Nat} (e : Step m x d m' x') :
    2^m'*x'^3=2^(m+1)*(Q m x)^3 := by
  obtain ⟨_,hm,_,he⟩ := e
  rw [←he,hm,show m+3*d+1=m+1+d*3 by omega,Nat.pow_add,Nat.pow_mul,Nat.mul_pow,Nat.mul_assoc]

def commonM (j : Nat) := 3612686254+7046430720*j
def commonX (j : Nat) := 190569199636+371699220480*j

private theorem common_base (j : Nat) :
    2*commonX j+633=base (commonM j) ∧ commonM j%2=0 := by
  unfold commonX commonM base
  omega

theorem common_good (j : Nat) : Good (commonM j) (commonX j) := by
  have h := common_base j
  unfold Good s
  have hx : 633<commonX j := by unfold commonX; omega
  omega

/-- The common affine root is a genuine root of the positive ordinary forest. -/
theorem common_no_incoming (j m x d : Nat) (g : Good m x) :
    ¬Step m x d (commonM j) (commonX j) := by
  rintro ⟨hd,hm,hp,he⟩
  obtain ⟨hB,hpar⟩ := common_base j
  have hQ : Q m x=x+base m := by unfold Q; rw [←hp,hpar,Nat.mul_zero,Nat.add_zero]; rfl
  rw [hQ] at he
  by_cases hd1 : d=1
  · subst d
    change 2*commonX j=x+base m at he
    have hB' : base m+422=base (commonM j) := by unfold base; omega
    unfold Good at g
    omega
  · have hd2 : 2≤d := by omega
    have hpow : 4≤(2:Nat)^d := by simpa using Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hd2
    have hMul := Nat.mul_le_mul_right (commonX j) hpow
    rw [he] at hMul
    have hB' : base m+633≤base (commonM j) := by unfold base; omega
    unfold Good at g
    omega

structure Ray where
  m0 : Nat
  x0 : Nat
  dx : Nat
  deriving DecidableEq, Repr

def Ray.m (r : Ray) (j : Nat) := r.m0+7046430720*j
def Ray.x (r : Ray) (j : Nat) := r.x0+r.dx*j
def Ray.slope (r : Ray) := r.dx+743398440960
def Ray.child (r : Ray) (d : Nat) : Ray :=
  ⟨r.m0+3*d+1,Q r.m0 r.x0/2^d,r.slope/2^d⟩

def commonRay : Ray := ⟨3612686254,190569199636,371699220480⟩
def dRay : Ray := ⟨3612686289,79465868075,154995671040⟩
def lRay : Ray := ⟨3612686322,273974307270,534378245520⟩
def pRay : Ray := ⟨3612686327,74448864438,145210162020⟩

private theorem ray_base (r : Ray) (j : Nat) :
    base (r.m j)=base r.m0+743398440960*j := by
  unfold Ray.m base
  omega

private theorem ray_A (r : Ray) (j : Nat) : A (r.m j) (r.x j)=A r.m0 r.x0+r.slope*j := by
  unfold A Ray.x Ray.slope
  rw [ray_base,Nat.add_mul]
  omega

private theorem ray_parity (r : Ray) (j : Nat) (h : r.dx%2=0) :
    A (r.m j) (r.x j)%2=A r.m0 r.x0%2 := by
  rw [ray_A,Nat.add_mod,Nat.mul_mod]
  have hs : r.slope%2=0 := by unfold Ray.slope; omega
  rw [hs,Nat.zero_mul,Nat.zero_mod,Nat.add_zero,Nat.mod_mod]

private theorem ray_Q (r : Ray) (j : Nat) (h : r.dx%2=0) :
    Q (r.m j) (r.x j)=Q r.m0 r.x0+r.slope*j := by
  unfold Q
  rw [ray_parity r j h,ray_A]
  omega

private theorem pow_dvd_exact {q w d : Nat} (h : q%2^(w+1)=2^w) : (2^d∣q) ↔ d≤w := by
  have hpow : (2:Nat)^w∣2^(w+1) := Nat.pow_dvd_pow 2 (by omega)
  have hW : (2:Nat)^w∣q := by
    apply Nat.dvd_of_mod_eq_zero
    rw [←Nat.mod_mod_of_dvd q hpow,h,Nat.mod_self]
  constructor
  · intro hD
    by_cases hd : d≤w
    · exact hd
    · have hh : (2:Nat)^(w+1)∣q := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hD
      have hz := Nat.mod_eq_zero_of_dvd hh
      rw [h] at hz
      exact False.elim ((Nat.ne_of_gt (Nat.two_pow_pos w)) hz)
  · intro hd
    exact Nat.dvd_trans (Nat.pow_dvd_pow 2 hd) hW

/-- A single checked valuation certifies the exact legal costs on the whole ray. -/
theorem ray_cost_iff (r : Ray) (j w d : Nat) (he : r.dx%2=0)
    (hval : Q r.m0 r.x0%2^(w+1)=2^w)
    (hslope : 2^(w+1)∣r.slope) :
    (∃ m' x', Step (r.m j) (r.x j) d m' x') ↔
      0<d ∧ d≤w ∧ (r.m0+3*d+1)%2=A r.m0 r.x0%2 := by
  have hval' : Q (r.m j) (r.x j)%2^(w+1)=2^w := by
    rw [ray_Q r j he,Nat.add_mod,hval]
    have hd := Nat.dvd_trans hslope (Nat.dvd_mul_right _ j)
    rw [Nat.mod_eq_zero_of_dvd hd,Nat.add_zero]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  have hpar := ray_parity r j he
  have hm : (r.m j+3*d+1)%2=(r.m0+3*d+1)%2 := by unfold Ray.m; omega
  constructor
  · rintro ⟨m',x',hd,hM,hP,hQ⟩
    exact ⟨hd,(pow_dvd_exact hval').mp ⟨x',hQ.symm⟩,by omega⟩
  · rintro ⟨hd,hW,hP⟩
    obtain ⟨z,hz⟩ := (pow_dvd_exact hval').mpr hW
    exact ⟨r.m j+3*d+1,z,hd,rfl,by omega,hz.symm⟩

/-- Exact child ray, without enumerating any parameter value. -/
theorem ray_child_step (r : Ray) (j d : Nat) (he : r.dx%2=0)
    (hd : 0<d) (hp : (r.m0+3*d+1)%2=A r.m0 r.x0%2)
    (hq : 2^d∣Q r.m0 r.x0) (hs : 2^d∣r.slope) :
    Step (r.m j) (r.x j) d ((r.child d).m j) ((r.child d).x j) := by
  have hm : (r.child d).m j=r.m j+3*d+1 := by simp only [Ray.child,Ray.m]; omega
  have hp' : ((r.child d).m j)%2=A (r.m j) (r.x j)%2 := by
    rw [hm,ray_parity r j he]
    unfold Ray.m
    omega
  refine ⟨hd,hm,hp',?_⟩
  change 2^d*(Q r.m0 r.x0/2^d + (r.slope/2^d)*j)=Q (r.m j) (r.x j)
  rw [Nat.mul_add,←Nat.mul_assoc,Nat.mul_div_cancel' hq,Nat.mul_div_cancel' hs,ray_Q r j he]

#print axioms step_good
#print axioms scalar_iff
#print axioms decode_exists
#print axioms incoming_unique
#print axioms child_iff_not_bad
#print axioms sibling_mass_cube
#print axioms common_good
#print axioms common_no_incoming
#print axioms ray_cost_iff
#print axioms ray_child_step

/-- Infinite ordinary scalar branch from a given vertex. -/
def Infinite (m x : Nat) : Prop :=
  ∃ M X D : Nat → Nat, M 0=m ∧ X 0=x ∧
    ∀ n, Step (M n) (X n) (D n) (M (n+1)) (X (n+1))

theorem infinite_next {m x : Nat} (h : Infinite m x) :
    ∃ d m' x', Step m x d m' x' ∧ Infinite m' x' := by
  obtain ⟨M,X,D,hM,hX,hE⟩ := h
  refine ⟨D 0,M 1,X 1,?_,?_⟩
  · simpa [hM,hX] using hE 0
  · exact ⟨fun n => M (n+1),fun n => X (n+1),fun n => D (n+1),rfl,rfl,
      fun n => hE (n+1)⟩

def Keep (r : Ray) : Prop := r=dRay ∨ r=lRay ∨ r=pRay
instance (r : Ray) : Decidable (Keep r) := by unfold Keep; infer_instance

def valAux : Nat → Nat → Nat
  | 0,_ => 0
  | f+1,n => if n%2=0 then 1+valAux f (n/2) else 0

def cutChecked : Nat → Ray → Bool
  | 0,r => decide (Keep r)
  | f+1,r => if Keep r then true else
    let w := valAux 64 (Q r.m0 r.x0)
    decide (r.dx%2=0 ∧ Q r.m0 r.x0%2^(w+1)=2^w ∧ 2^(w+1)∣r.slope) &&
    (List.range (w+1)).all (fun d =>
      if 0<d ∧ (r.m0+3*d+1)%2=A r.m0 r.x0%2 then cutChecked f (r.child d) else true)

theorem cut_sound (f : Nat) (r : Ray) (j : Nat) (h : cutChecked f r=true)
    (safe : ∀ t, Keep t → ¬Infinite (t.m j) (t.x j)) : ¬Infinite (r.m j) (r.x j) := by
  induction f generalizing r with
  | zero => exact safe r (of_decide_eq_true h)
  | succ f ih =>
    by_cases hk : Keep r
    · exact safe r hk
    · simp only [cutChecked,hk,if_false,Bool.and_eq_true,decide_eq_true_eq] at h
      obtain ⟨⟨he,hv,hs⟩,hall⟩ := h
      intro hi
      obtain ⟨d,m',x',hstep,hinf⟩ := infinite_next hi
      let w := valAux 64 (Q r.m0 r.x0)
      have hc := (ray_cost_iff r j w d he hv hs).mp ⟨m',x',hstep⟩
      obtain ⟨hd,hw,hp⟩ := hc
      have hq : 2^d∣Q r.m0 r.x0 := (pow_dvd_exact hv).mpr hw
      have hs' : 2^d∣r.slope := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega : d≤w+1)) hs
      have he' := ray_child_step r j d he hd hp hq hs'
      have hm : m'=(r.child d).m j := by have h1 := hstep.2.1; have h2 := he'.2.1; omega
      have hx : x'=(r.child d).x j := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos d) (hstep.2.2.2.trans he'.2.2.2.symm)
      have hh := List.all_eq_true.mp hall d (List.mem_range.mpr (by omega : d<w+1))
      simp only [hd,hp,and_self,if_true] at hh
      exact ih (r.child d) hh (by simpa [hm,hx] using hinf)

theorem common_cut_checked : cutChecked 12 commonRay=true := by decide

theorem common_cut (j : Nat)
    (hD : ¬Infinite (dRay.m j) (dRay.x j))
    (hL : ¬Infinite (lRay.m j) (lRay.x j))
    (hP : ¬Infinite (pRay.m j) (pRay.x j)) : ¬Infinite (commonRay.m j) (commonRay.x j) := by
  apply cut_sound 12 commonRay j common_cut_checked
  intro t ht
  rcases ht with h|h|h <;> subst t <;> assumption

#print axioms cut_sound
#print axioms common_cut_checked
#print axioms common_cut
def sourceShadow (a b j : Nat) := a*(22155*j+17300)-22155*b

theorem source_ray_coordinates (j : Nat) :
    105*U (dRay.m j) (dRay.x j)=sourceShadow 1469153280 393975148 j ∧
    105*V (dRay.m j) (dRay.x j)=sourceShadow 2788638720 747814654 j ∧
    105*U (lRay.m j) (lRay.x j)=sourceShadow 5065196640 1358307257 j ∧
    105*V (lRay.m j) (lRay.x j)=sourceShadow 990617040 265648583 j ∧
    105*U (pRay.m j) (pRay.x j)=sourceShadow 1376399640 369101882 j ∧
    105*V (pRay.m j) (pRay.x j)=sourceShadow 2835015540 760251268 j := by
  simp only [sourceShadow,U,V,base,s,Ray.m,Ray.x,dRay,lRay,pRay]
  omega

#print axioms source_ray_coordinates
end BB6.Agent19Scalar
