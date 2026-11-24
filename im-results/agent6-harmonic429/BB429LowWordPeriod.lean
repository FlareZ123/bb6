import BB429LowWord
import BB429LowPeriod
import Lean.Elab.Tactic.Omega

namespace BB429.LowWord
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

structure Linear where
  x : Int
  d : Int
  c : Int
  deriving Repr, DecidableEq

def Linear.eval (l : Linear) (X d : Int) : Int := l.x*X+l.d*d+l.c

def guardForms (v : Move) (f : Form) : List Linear :=
  match v with
  | .f => [⟨72-2*f.a,1-2*f.b,f.r+9-2*f.c⟩]
  | .oe => [⟨2*f.a-72,2*f.b-1,2*f.c-f.r-19⟩, ⟨72-f.a,1-f.b,f.r-f.c+3⟩]
  | .oo => [⟨2*f.a-72,2*f.b-1,2*f.c-f.r-17⟩]

def phaseOK (v : Move) (f : Form) : Prop :=
  match v with
  | .f => True
  | .oe => (f.r+2)%4=1
  | .oo => (f.r+2)%4=3

def phases : List Move → Form → Prop
  | [],_ => True
  | v::vs,f => phaseOK v f ∧ phases vs (symStep v f)

def forms : List Move → Form → List Linear
  | [],_ => []
  | v::vs,f => guardForms v f ++ forms vs (symStep v f)

theorem guard_iff (v : Move) (f : Form) (X d : Int) (hd : d%4=2) :
    guard v (eval f X d) ↔ phaseOK v f ∧ ∀ l ∈ guardForms v f, 0≤l.eval X d := by
  cases v <;> simp only [guard,eval,phaseOK,guardForms,List.mem_cons,List.not_mem_nil,or_false,
    forall_eq_or_imp,forall_eq,Linear.eval,Int.sub_mul,Int.mul_assoc,Int.mul_add,Int.one_mul,true_and] <;> omega

theorem legal_iff (vs : List Move) (f : Form) (X d : Int) (hd : d%4=2) :
    legal vs (eval f X d) ↔ phases vs f ∧ ∀ l ∈ forms vs f, 0≤l.eval X d := by
  induction vs generalizing f with
  | nil => simp [legal,phases,forms]
  | cons v vs ih =>
    simp only [legal,phases,forms]
    rw [←eval_step,guard_iff v f X d hd,ih (symStep v f)]
    constructor
    · rintro ⟨⟨hp,hg⟩,ht,hall⟩
      refine ⟨⟨hp,ht⟩,?_⟩
      intro l hl
      rcases List.mem_append.mp hl with h|h
      · exact hg l h
      · exact hall l h
    · rintro ⟨⟨hp,ht⟩,hall⟩
      exact ⟨⟨hp,fun l hl => hall l (List.mem_append_left _ hl)⟩,
        ht,fun l hl => hall l (List.mem_append_right _ hl)⟩

def Linear.elim (l : Linear) (M K H X : Int) : Int :=
  (M*l.x+K*l.d)*X+(M*l.c-H*l.d)

/-- Multiplying an affine guard by the positive modulus removes d exactly. -/
theorem elim_eq (l : Linear) (M K H X d : Int) (h : M*d=K*X-H) :
    M*l.eval X d=l.elim M K H X := by
  unfold Linear.eval Linear.elim
  rw [Int.mul_add,Int.mul_add,show M*(l.d*d)=(M*d)*l.d by ac_rfl,h]
  simp only [Int.add_mul,Int.sub_mul]
  have h1 : M*(l.x*X)=M*l.x*X := by ac_rfl
  have h2 : K*X*l.d=K*l.d*X := by ac_rfl
  omega

theorem elim_nonneg (l : Linear) (M K H X d : Int) (hM : 0<M) (h : M*d=K*X-H) :
    0≤l.eval X d ↔ 0≤l.elim M K H X := by
  rw [←elim_eq l M K H X d h]
  constructor
  · intro hp
    exact Int.mul_nonneg (by omega) hp
  · intro hp
    have hh : M*0≤M*l.eval X d := by simpa using hp
    exact Int.le_of_mul_le_mul_left hh hM

def allForms (vs : List Move) : List Linear := ⟨0,1,-6⟩ :: forms vs initial

/-- The exact congruence for d=2 mod 4 after eliminating d. -/
def congruence (M K H X : Int) : Prop := (4*M) ∣ (K*X-H-2*M)

theorem congruence_iff (M K H X : Int) (hM : 0<M) :
    congruence M K H X ↔ ∃ d : Int, d%4=2 ∧ M*d=K*X-H := by
  unfold congruence
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨4*z+2,by omega,?_⟩
    rw [Int.mul_add,show M*(4*z)=4*M*z by ac_rfl]
    omega
  · rintro ⟨d,hd,h⟩
    refine ⟨d/4,?_⟩
    have he : d=4*(d/4)+2 := by omega
    conv at h => lhs; rw [he,Int.mul_add,show M*(4*(d/4))=4*M*(d/4) by ac_rfl]
    omega

/-- Exact test on the scale alone: a congruence plus a finite list of
    affine inequalities in X. No simulation of intermediate counters. -/
def ScaleTest (vs : List Move) (X : Int) : Prop :=
  let f := symbolic vs initial
  phases vs initial ∧ congruence (Modulus f) (Coefficient f) (Offset f) X ∧
    ∀ l ∈ allForms vs, 0≤l.elim (Modulus f) (Coefficient f) (Offset f) X

theorem terminal_iff_scale (m : Nat) (vs : List Move) :
    Terminal m vs ↔ 1≤m ∧ ScaleTest vs ((16:Int)^m) := by
  let f := symbolic vs initial
  let M := Modulus f
  let K := Coefficient f
  let H := Offset f
  let X := (16:Int)^m
  have hM : 0<M := (modulus_positive_odd vs).1
  constructor
  · rintro ⟨hm,d,hd,hmod,hl,hg⟩
    have hdmod : (d:Int)%4=2 := by omega
    have ⟨hp,hall⟩ := (legal_iff vs initial X d hdmod).mp hl
    refine ⟨hm,hp,(congruence_iff M K H X hM).mpr ⟨d,hdmod,hg⟩,?_⟩
    intro l hl
    apply (elim_nonneg l M K H X d hM hg).mp
    rcases List.mem_cons.mp hl with h|h
    · subst l
      simp only [Linear.eval,Int.zero_mul,Int.one_mul,Int.zero_add]
      omega
    · exact hall l h
  · rintro ⟨hm,hp,hc,hall⟩
    obtain ⟨d,hdmod,hg⟩ := (congruence_iff M K H X hM).mp hc
    have hd := (elim_nonneg ⟨0,1,-6⟩ M K H X d hM hg).mpr (hall _ (by simp [allForms]))
    simp only [Linear.eval,Int.zero_mul,Int.one_mul,Int.zero_add] at hd
    have hdpos : 6≤d := by omega
    let dn := d.toNat
    have hdn : (dn:Int)=d := Int.toNat_of_nonneg (by omega)
    have hdN : 6≤dn := by omega
    have hmodN : dn%4=2 := by omega
    have hleg : legal vs (eval initial X d) := by
      apply (legal_iff vs initial X d hdmod).mpr
      refine ⟨hp,?_⟩
      intro l hl
      exact (elim_nonneg l M K H X d hM hg).mpr (hall l (List.mem_cons_of_mem _ hl))
    refine ⟨hm,dn,hdN,hmodN,?_,?_⟩
    · simpa only [hdn] using hleg
    · simpa only [hdn] using hg

/-- The guard inequalities define a genuine interval in X: a point between
    two feasible endpoints satisfies every guard. -/
theorem affine_between (a b X Y Z : Int) (hXY : X≤Y) (hYZ : Y≤Z)
    (hx : 0≤a*X+b) (hz : 0≤a*Z+b) : 0≤a*Y+b := by
  by_cases ha : 0≤a
  · have hh := Int.mul_le_mul_of_nonneg_left hXY ha
    omega
  · have hh := Int.mul_le_mul_of_nonpos_left (show a≤0 by omega) hYZ
    omega

theorem guard_interval (vs : List Move) (X Y Z : Int) (hXY : X≤Y) (hYZ : Y≤Z)
    (hx : ScaleTest vs X) (hz : ScaleTest vs Z)
    (hc : let f := symbolic vs initial; congruence (Modulus f) (Coefficient f) (Offset f) Y) :
    ScaleTest vs Y := by
  refine ⟨hx.1,hc,?_⟩
  intro l hl
  exact affine_between _ _ X Y Z hXY hYZ (hx.2.2 l hl) (hz.2.2 l hl)

#print axioms terminal_iff_scale
#print axioms guard_interval
end BB429.LowWord
