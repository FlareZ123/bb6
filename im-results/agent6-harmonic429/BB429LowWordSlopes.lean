import BB429LowWordPeriod
import Lean

namespace BB429.LowWord
namespace Slopes

/-- The binary number encoded by the F=0, Oe/Oo=1 branch digits. -/
def code : List Bool → Int
  | [] => 0
  | b::bs => (if b then 1 else 0) * 2^bs.length + code bs

theorem code_bounds (bs : List Bool) : 0 ≤ code bs ∧ code bs < 2^bs.length := by
  induction bs with
  | nil => simp [code]
  | cons b bs ih =>
    cases b <;> simp [code, List.length_cons, Int.pow_succ] <;> omega

theorem code_append (p q : List Bool) : code (p++q) = code p * 2^q.length + code q := by
  induction p with
  | nil => simp [code]
  | cons b bs ih =>
    simp only [List.cons_append, code, List.length_append, Int.pow_add, ih, Int.add_mul, Int.mul_assoc]
    omega

/-- The eliminated slope of the F guard at a prefix of length j,
    followed by a suffix of length k with binary value q. -/
def fSlope (j k : Nat) (p q : Int) : Int :=
  let D := (2:Int)^j
  let E := (2:Int)^k
  let M := 2*(p*E+q)+1
  let P := 2*p+1
  let K := 96*(D*E)-72*M
  M*(72*P-96*D)+K*P

theorem fSlope_eq (j k : Nat) (p q : Int) :
    fSlope j k p q = 96*2^j*(2^k-(2*q+1)) := by
  unfold fSlope
  grind

/-- The extra Oe guard w≥3 has this eliminated slope. -/
def wSlope (j k : Nat) (p q : Int) : Int :=
  let D := (2:Int)^j
  let E := (2:Int)^k
  let M := 2*(p*E+q)+1
  let K := 96*(D*E)-72*M
  M*(72*(p+1)-48*D)+K*(p+1)

theorem wSlope_eq (j k : Nat) (p q : Int) :
    wSlope j k p q = 48*2^j*(2*2^k-(2*q+1)) := by
  unfold wSlope
  grind

theorem fSlope_pos (p q : List Bool) :
    0 < fSlope p.length (false::q).length (code p) (code (false::q)) := by
  rw [fSlope_eq]
  have h := code_bounds q
  simp only [code, Bool.false_eq_true, ↓reduceIte, Int.zero_mul, Int.zero_add,
    List.length_cons, Int.pow_succ]
  apply Int.mul_pos
  · exact Int.mul_pos (by decide) (Int.pow_pos (by decide))
  · omega

theorem oSlope_pos (p q : List Bool) :
    0 < -fSlope p.length (true::q).length (code p) (code (true::q)) := by
  rw [fSlope_eq, ← Int.mul_neg]
  have h := code_bounds q
  simp only [code, ↓reduceIte, Int.one_mul, List.length_cons, Int.pow_succ]
  apply Int.mul_pos
  · exact Int.mul_pos (by decide) (Int.pow_pos (by decide))
  · omega

theorem wSlope_pos (p q : List Bool) :
    0 < wSlope p.length (true::q).length (code p) (code (true::q)) := by
  rw [wSlope_eq]
  have h := code_bounds (true::q)
  apply Int.mul_pos
  · exact Int.mul_pos (by decide) (Int.pow_pos (by decide))
  · omega

def bit : Move → Bool
  | .f => false
  | _ => true

def bits (vs : List Move) : List Bool := vs.map bit

@[simp] theorem bits_length (vs : List Move) : (bits vs).length=vs.length := by simp [bits]

theorem sym_bits (vs : List Move) (f : Form) :
    -(symbolic vs f).b = -f.b*2^vs.length + code (bits vs) := by
  induction vs generalizing f with
  | nil => simp [symbolic, bits, code]
  | cons v vs ih =>
    simp only [symbolic, ih, List.length_cons, bits, List.map_cons, code, List.length_map, Int.pow_succ]
    cases v <;> simp [symStep, bit] <;> grind

theorem prefix_b (p : List Move) : (symbolic p initial).b = -code (bits p) := by
  have h := sym_bits p initial
  change -(symbolic p initial).b = 0*2^p.length + code (bits p) at h
  omega

theorem prefix_a (p : List Move) : (symbolic p initial).a = 48*2^p.length-72*code (bits p) := by
  have h := (symbolic_coefficients p initial (by decide)).2
  rw [prefix_b] at h
  change (symbolic p initial).a - 72 * -code (bits p) = (2:Int)^p.length * 48 at h
  grind

theorem mod_append (p q : List Move) :
    Modulus (symbolic (p++q) initial) = 2*(code (bits p)*2^q.length+code (bits q))+1 := by
  unfold Modulus
  rw [prefix_b]
  simp only [bits,List.map_append,code_append,List.length_map]
  omega

theorem coef_append (p q : List Move) :
    Coefficient (symbolic (p++q) initial) =
      96*((2:Int)^p.length*2^q.length)-72*(2*(code (bits p)*2^q.length+code (bits q))+1) := by
  rw [coefficient_identity,mod_append,List.length_append,Int.pow_add]

def slope (f : Form) (l : Linear) : Int := Modulus f*l.x+Coefficient f*l.d

theorem slope_guard (p q : List Move) (v : Move) (l : Linear)
    (hl : l ∈ guardForms v (symbolic p initial)) :
    0 < slope (symbolic (p++v::q) initial) l := by
  have hM := mod_append p (v::q)
  have hK := coef_append p (v::q)
  have ha := prefix_a p
  have hb := prefix_b p
  have hf := fSlope_pos (bits p) (bits q)
  have ho := oSlope_pos (bits p) (bits q)
  have hw := wSlope_pos (bits p) (bits q)
  simp only [bits_length,List.length_cons] at hf ho hw
  cases v with
  | f =>
    simp only [guardForms,List.mem_cons,List.not_mem_nil,or_false] at hl
    subst l
    simp only [slope,hM,hK,ha,hb,List.length_cons,show bits (.f::q)=false::bits q from rfl]
    simp only [fSlope] at hf
    grind
  | oe =>
    simp only [guardForms,List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with h|h <;> subst l
    · simp only [slope,hM,hK,ha,hb,List.length_cons,show bits (.oe::q)=true::bits q from rfl]
      simp only [fSlope] at ho
      grind
    · simp only [slope,hM,hK,ha,hb,List.length_cons,show bits (.oe::q)=true::bits q from rfl]
      simp only [wSlope] at hw
      grind
  | oo =>
    simp only [guardForms,List.mem_cons,List.not_mem_nil,or_false] at hl
    subst l
    simp only [slope,hM,hK,ha,hb,List.length_cons,show bits (.oo::q)=true::bits q from rfl]
    simp only [fSlope] at ho
    grind

theorem symbolic_append (p q : List Move) (f : Form) :
    symbolic (p++q) f = symbolic q (symbolic p f) := by
  induction p generalizing f with
  | nil => rfl
  | cons v p ih => simp only [List.cons_append,symbolic,ih]

theorem forms_split (vs : List Move) (f : Form) (l : Linear) (hl : l∈forms vs f) :
    ∃ p v q, vs=p++v::q ∧ l∈guardForms v (symbolic p f) := by
  induction vs generalizing f with
  | nil => simp [forms] at hl
  | cons v vs ih =>
    simp only [forms,List.mem_append] at hl
    rcases hl with h|h
    · exact ⟨[],v,vs,rfl,h⟩
    · obtain ⟨p,w,q,he,hh⟩ := ih (symStep v f) h
      exact ⟨v::p,w,q,by simp [he],hh⟩

theorem all_branch_slopes_pos (vs : List Move) (l : Linear) (hl : l ∈ forms vs initial) :
    0 < slope (symbolic vs initial) l := by
  obtain ⟨p,v,q,he,hh⟩ := forms_split vs initial l hl
  rw [he]
  exact slope_guard p q v l hh

theorem phase_pair_bound (vs : List Move) (f : Form) (hr : f.r%2=1)
    (hp : phases vs f) (he : vs.length%2=0) :
    3*(2*code (bits vs)+1) ≤ 4*(2:Int)^vs.length-1 := by
  cases vs with
  | nil => decide
  | cons v tail =>
    cases tail with
    | nil => simp at he
    | cons w q =>
      have hsecond : phaseOK w (symStep v f) := hp.2.1
      have hpar : (symStep v f).r%2=0 := by cases v <;> simp [symStep] <;> omega
      have hw : w=.f := by cases w <;> simp [phaseOK] at hsecond ⊢ <;> omega
      subst w
      have hodd : (symStep .f (symStep v f)).r%2=1 := by change ((symStep v f).r+3)%2=1; omega
      have hq : q.length%2=0 := by simp only [List.length_cons] at he; omega
      have ih := phase_pair_bound q (symStep .f (symStep v f)) hodd hp.2.2 hq
      have hpow : 0 < (2:Int)^q.length := Int.pow_pos (by decide)
      cases v <;> simp [bits,bit,code,List.length_cons,Int.pow_succ] at ih ⊢ <;> omega
termination_by vs.length

theorem coefficient_positive (vs : List Move) (hp : phases vs initial) (he : vs.length%2=0) :
    24 ≤ Coefficient (symbolic vs initial) := by
  have h := phase_pair_bound vs initial (by decide) hp he
  rw [coefficient_identity]
  unfold Modulus
  rw [prefix_b]
  omega

theorem rank_parity (vs : List Move) (f : Form) :
    (symbolic vs f).r%2=(f.r+(vs.length:Int))%2 := by
  induction vs generalizing f with
  | nil => simp [symbolic]
  | cons v vs ih =>
    simp only [symbolic,ih,List.length_cons,Int.natCast_add,Int.natCast_one]
    cases v <;> simp [symStep] <;> omega

theorem even_length_of_congruence (vs : List Move) (X : Int)
    (h : let f := symbolic vs initial; congruence (Modulus f) (Coefficient f) (Offset f) X) :
    vs.length%2=0 := by
  let f := symbolic vs initial
  change (4*Modulus f) ∣ (Coefficient f*X-Offset f-2*Modulus f) at h
  obtain ⟨z,hz⟩ := h
  unfold Modulus Coefficient Offset at hz
  have he : f.r+13=2*(f.a*X-36*X+f.c-(1-2*f.b)-2*(1-2*f.b)*z) := by grind
  have hr : f.r%2=1 := by omega
  have hh := rank_parity vs initial
  change f.r%2=(3+(vs.length:Int))%2 at hh
  omega

theorem all_slopes_pos (vs : List Move) (hp : phases vs initial) (he : vs.length%2=0)
    (l : Linear) (hl : l∈allForms vs) : 0<slope (symbolic vs initial) l := by
  rcases List.mem_cons.mp hl with h|h
  · subst l
    have hk := coefficient_positive vs hp he
    simp [slope]
    omega
  · exact all_branch_slopes_pos vs l h

theorem guards_monotone (vs : List Move) (X Y : Int) (hXY : X≤Y)
    (hp : phases vs initial) (he : vs.length%2=0)
    (hX : let f := symbolic vs initial; ∀ l∈allForms vs,
      0≤l.elim (Modulus f) (Coefficient f) (Offset f) X) :
    let f := symbolic vs initial; ∀ l∈allForms vs,
      0≤l.elim (Modulus f) (Coefficient f) (Offset f) Y := by
  intro f l hl
  have hs := all_slopes_pos vs hp he l hl
  change 0<slope f l at hs
  have h := Int.mul_le_mul_of_nonneg_left hXY (show 0≤slope f l by exact Int.le_of_lt hs)
  have hx := hX l hl
  change 0≤slope f l*X+(Modulus f*l.c-Offset f*l.d) at hx
  change 0≤slope f l*Y+(Modulus f*l.c-Offset f*l.d)
  omega

/-- The guard set contains a full final ray whenever the phase is valid and
    the word has even length. This removes the guard feasibility question. -/
theorem guards_eventually (vs : List Move) (hp : phases vs initial) (he : vs.length%2=0) :
    ∃ B : Nat, ∀ X : Int, B≤X → let f := symbolic vs initial; ∀ l∈allForms vs,
      0≤l.elim (Modulus f) (Coefficient f) (Offset f) X := by
  let f := symbolic vs initial
  let offs := fun l : Linear => (Modulus f*l.c-Offset f*l.d).natAbs
  let B := ((allForms vs).map offs).sum
  refine ⟨B,?_⟩
  intro X hX g l hl
  have hs := all_slopes_pos vs hp he l hl
  change 0<slope f l at hs
  have hmul := Int.mul_le_mul_of_nonneg_right (show 1≤slope f l by omega) (show 0≤X by omega)
  rw [Int.one_mul] at hmul
  have hmem : offs l ∈ (allForms vs).map offs := List.mem_map_of_mem hl
  have hsum : offs l ≤ B := by
    dsimp [B]
    generalize ((allForms vs).map offs)=xs at hmem ⊢
    induction xs with
    | nil => simp at hmem
    | cons a xs ih =>
      simp only [List.mem_cons] at hmem
      rw [List.sum_cons]
      rcases hmem with h|h
      · omega
      · have hh := ih h; omega
  have habs := Int.le_natAbs (a := -(Modulus f*l.c-Offset f*l.d))
  rw [Int.natAbs_neg] at habs
  change -(Modulus f*l.c-Offset f*l.d)≤(offs l:Int) at habs
  change 0≤slope f l*X+(Modulus f*l.c-Offset f*l.d)
  omega

theorem rank_mod4 (vs : List Move) (f : Form) :
    (symbolic vs f).r%4=(f.r+3*(vs.length:Int))%4 := by
  induction vs generalizing f with
  | nil => simp [symbolic]
  | cons v vs ih =>
    simp only [symbolic,ih,List.length_cons,Int.natCast_add,Int.natCast_one]
    cases v <;> simp [symStep] <;> omega

theorem even_c (vs : List Move) (f : Form) (hc : f.c%2=0) (hp : phases vs f) :
    (symbolic vs f).c%2=0 := by
  induction vs generalizing f with
  | nil => exact hc
  | cons v vs ih =>
    have hs : (symStep v f).c%2=0 := by
      have h := hp.1
      cases v <;> simp [phaseOK,symStep] at h ⊢ <;> omega
    exact ih (symStep v f) hs hp.2

theorem length_mod4_of_phase_congruence (vs : List Move) (X : Int)
    (hp : phases vs initial)
    (h : let f := symbolic vs initial; congruence (Modulus f) (Coefficient f) (Offset f) X) :
    vs.length%4=2 := by
  let f := symbolic vs initial
  change (4*Modulus f) ∣ (Coefficient f*X-Offset f-2*Modulus f) at h
  obtain ⟨z,hz⟩ := h
  have hk := coefficient_identity vs
  change Coefficient f=96*(2:Int)^vs.length-72*Modulus f at hk
  have hc := even_c vs initial (by decide) hp
  change f.c%2=0 at hc
  have hr := rank_mod4 vs initial
  change f.r%4=(3+3*(vs.length:Int))%4 at hr
  have he : f.r+13=4*(24*(2:Int)^vs.length*X-18*Modulus f*X+f.c/2+f.b-Modulus f*z)-2 := by
    unfold Offset at hz
    have hc' : f.c=2*(f.c/2) := by omega
    have hm : Modulus f=1-2*f.b := rfl
    grind
  omega

/-- The exact guard ray implies an abstract cofinality theorem: once the
    congruence is known to recur periodically in the scale exponent, no
    branch inequality can remove its sufficiently large occurrences. -/
theorem cofinal_scale_test (vs : List Move) (m0 p : Nat) (hp : 0<p)
    (hphase : phases vs initial)
    (hperiod : let f := symbolic vs initial; ∀ m : Nat, m%p=m0%p →
       congruence (Modulus f) (Coefficient f) (Offset f) ((16:Int)^m)) :
    ∀ L : Nat, ∃ m ≥ L, 1≤m ∧ ScaleTest vs ((16:Int)^m) := by
  have hc := hperiod m0 rfl
  have he := even_length_of_congruence vs _ hc
  obtain ⟨B,hB⟩ := guards_eventually vs hphase he
  intro L
  let m := m0+p*(L+B+1)
  have hm : m%p=m0%p := by dsimp [m]; simp [Nat.add_mod]
  have hmge : L+B+1≤m := by
    dsimp [m]
    have h := Nat.mul_le_mul_right (L+B+1) (show 1≤p by omega)
    omega
  have powbound : ∀ n : Nat, n+1≤16^n := by
    intro n
    induction n with
    | zero => decide
    | succ n ih => rw [Nat.pow_succ]; omega
  have hpow : (B:Int)≤(16:Int)^m := by
    rw [show (16:Int)^m=((16^m:Nat):Int) by exact (Int.natCast_pow 16 m).symm]
    have h := powbound m
    omega
  exact ⟨m,by omega,by omega,hphase,hperiod m hm,hB _ hpow⟩

#print axioms length_mod4_of_phase_congruence
#print axioms cofinal_scale_test
#print axioms all_branch_slopes_pos
#print axioms coefficient_positive
#print axioms even_length_of_congruence
#print axioms guards_monotone
#print axioms guards_eventually
#print axioms code_append
#print axioms fSlope_eq
#print axioms wSlope_eq
#print axioms fSlope_pos
#print axioms oSlope_pos
#print axioms wSlope_pos
end Slopes
end BB429.LowWord
