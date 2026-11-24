import Lean
import Lean.Elab.Tactic.Omega

namespace NeedleRotation

abbrev Term := Int × Nat

def value : List Term → Int
  | [] => 0
  | (c,e)::ts => c * 2^e + value ts

def rotateTerm (m h : Nat) (t : Term) : Term :=
  (t.1 * (-3)^((t.2+h)/m), (t.2+h)%m)

def rotate (m h : Nat) (ts : List Term) : List Term := ts.map (rotateTerm m h)

def denominator (m : Nat) : Int := 2^m+3

theorem dvd_power_difference (D x y : Int) (hd : D ∣ x-y) (q : Nat) : D ∣ x^q-y^q := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 : D ∣ (x^q-y^q)*x := Int.dvd_mul_of_dvd_left ih
    have h2 : D ∣ y^q*(x-y) := Int.dvd_mul_of_dvd_right hd
    have he : x^(q+1)-y^(q+1)=(x^q-y^q)*x+y^q*(x-y) := by
      simp only [Int.pow_succ]
      grind
    rw [he]
    exact Int.dvd_add h1 h2

theorem term_congruence (m h : Nat) (t : Term) :
    denominator m ∣ 2^h*(t.1*2^t.2) - (rotateTerm m h t).1*2^(rotateTerm m h t).2 := by
  rcases t with ⟨c,e⟩
  let q := (e+h)/m
  let s := (e+h)%m
  have hd : denominator m ∣ (2:Int)^m-(-3) := by
    have he : (2:Int)^m-(-3)=denominator m := by simp [denominator]
    rw [he]
    exact Int.dvd_refl _
  have hp := dvd_power_difference (denominator m) ((2:Int)^m) (-3) hd q
  have hmul : denominator m ∣ c*2^s*(((2:Int)^m)^q-(-3)^q) := Int.dvd_mul_of_dvd_right hp
  have he : m*q+s=e+h := Nat.div_add_mod (e+h) m
  change denominator m ∣ (2:Int)^h*(c*2^e) - (c*(-3)^q)*2^s
  have hpow : (2:Int)^e * 2^h = ((2:Int)^m)^q * 2^s := by
    rw [←Int.pow_add, ←he, Int.pow_add, Int.pow_mul]
  have heq : (2:Int)^h*(c*2^e) - (c*(-3)^q)*2^s = c*2^s*(((2:Int)^m)^q-(-3)^q) := by
    rw [show (2:Int)^h*(c*2^e)=c*(2^e*2^h) by grind, hpow]
    grind
  rw [heq]
  exact hmul

theorem rotation_congruence (m h : Nat) (ts : List Term) :
    denominator m ∣ (2:Int)^h*value ts-value (rotate m h ts) := by
  induction ts with
  | nil => simp [value,rotate]
  | cons t ts ih =>
    rcases t with ⟨c,e⟩
    simp only [rotate,List.map_cons,value] at *
    rw [show (2:Int)^h*(c*2^e+value ts) -
      ((rotateTerm m h (c,e)).1*2^(rotateTerm m h (c,e)).2+value (List.map (rotateTerm m h) ts)) =
      ((2:Int)^h*(c*2^e)-(rotateTerm m h (c,e)).1*2^(rotateTerm m h (c,e)).2) +
      ((2:Int)^h*value ts-value (List.map (rotateTerm m h) ts)) by grind]
    exact Int.dvd_add (term_congruence m h (c,e)) ih

theorem rotated_divisibility (m h : Nat) (ts : List Term)
    (hd : denominator m ∣ value ts) : denominator m ∣ value (rotate m h ts) := by
  have h1 : denominator m ∣ (2:Int)^h*value ts := Int.dvd_mul_of_dvd_right hd
  have h2 := rotation_congruence m h ts
  have he : (2:Int)^h*value ts - ((2:Int)^h*value ts-value (rotate m h ts)) = value (rotate m h ts) := by omega
  rw [←he]
  exact Int.dvd_sub h1 h2

def mass : List Term → Nat
  | [] => 0
  | (c,_)::ts => c.natAbs + mass ts

theorem abs_value_le (ts : List Term) (E : Nat) (he : ∀ t ∈ ts, t.2 ≤ E) :
    (value ts).natAbs ≤ mass ts * 2^E := by
  induction ts with
  | nil => simp [value,mass]
  | cons t ts ih =>
    rcases t with ⟨c,e⟩
    have he0 := he (c,e) (by simp)
    have het : ∀ t ∈ ts, t.2 ≤ E := fun t ht => he t (by simp [ht])
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) he0
    calc
      (value ((c,e)::ts)).natAbs ≤ (c*(2:Int)^e).natAbs + (value ts).natAbs := by
        exact Int.natAbs_add_le _ _
      _ ≤ c.natAbs*2^E + mass ts*2^E := by
        rw [Int.natAbs_mul,Int.natAbs_pow]
        exact Nat.add_le_add (Nat.mul_le_mul_left _ hp) (ih het)
      _ = mass ((c,e)::ts)*2^E := by simp [mass,Nat.add_mul]

theorem rotation_zero_of_gap (m B h : Nat) (ts : List Term)
    (hB : B ≤ m) (he : ∀ t ∈ rotate m h ts, t.2 ≤ m-B)
    (hmass : mass (rotate m h ts) < 2^B)
    (hd : denominator m ∣ value ts) : value (rotate m h ts) = 0 := by
  have ha := abs_value_le (rotate m h ts) (m-B) he
  have hp : 0 < (2:Nat)^(m-B) := Nat.pow_pos (by decide)
  have hh := Nat.mul_lt_mul_of_pos_right hmass hp
  rw [←Nat.pow_add, Nat.add_comm B (m-B), Nat.sub_add_cancel hB] at hh
  have hsmall : (value (rotate m h ts)).natAbs < (denominator m).natAbs := by
    have heq : (denominator m).natAbs = 2^m+3 := by
      simp [denominator,Int.natAbs_pow,Int.natAbs_add_of_nonneg,Int.pow_nonneg]
    rw [heq]
    omega
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (rotated_divisibility m h ts hd) hsmall

theorem bad_shift_unique (m B e j k : Nat) (hB : 0 < B)
    (hj : j*B < m) (hk : k*B ≤ m-B)
    (hjk : j < k)
    (hbj : m-B < (e+j*B)%m)
    (hbk : m-B < (e+k*B)%m) : False := by
  have hm : 0 < m := by omega
  let d := (k-j)*B
  have hd1 : B ≤ d := by
    have hh := Nat.mul_le_mul_right B (show 1 ≤ k-j by omega)
    simpa [d] using hh
  have hdeq : j*B+d=k*B := by
    dsimp [d]
    rw [←Nat.add_mul, Nat.add_sub_of_le (Nat.le_of_lt hjk)]
  have hd2 : d ≤ m-B := by omega
  have hx : (e+j*B)%m < m := Nat.mod_lt _ hm
  have hs : (e+k*B)%m = ((e+j*B)%m+d)%m := by
    rw [←hdeq, ←Nat.add_assoc, Nat.add_mod, Nat.mod_eq_of_lt (show d<m by omega)]
  rw [hs, Nat.mod_eq_sub_mod (show (e+j*B)%m+d ≥ m by omega), Nat.mod_eq_of_lt (show (e+j*B)%m+d-m<m by omega)] at hbk
  omega

theorem exists_good_shift (es : List Nat) (m B : Nat)
    (hB : 0 < B) (hsize : (es.length+1)*B ≤ m) :
    ∃ h : Nat, h < m ∧ h ≤ m-B ∧ ∀ e ∈ es, (e+h)%m ≤ m-B := by
  classical
  let n := es.length+1
  change n*B ≤ m at hsize
  have hn : 0<n := by dsimp [n]; omega
  have hm : 0<m := by
    have hmul := Nat.mul_pos hn hB
    exact Nat.lt_of_lt_of_le hmul hsize
  have hcut : ∀ j<n, j*B ≤ m-B := by
    intro j hj
    have hh := Nat.mul_le_mul_right B (show j+1≤n by omega)
    rw [Nat.add_mul,Nat.one_mul] at hh
    omega
  let bad (e : Nat) := if h : ∃ j<n, m-B < (e+j*B)%m then Classical.choose h else n
  have hbad : ∀ e j, j<n → m-B < (e+j*B)%m → bad e=j := by
    intro e j hj hb
    have hx : ∃ k<n, m-B < (e+k*B)%m := ⟨j,hj,hb⟩
    simp only [bad, dite_eq_left hx]
    have hh := Classical.choose_spec hx
    rcases Nat.lt_trichotomy (Classical.choose hx) j with hlt|heq|hgt
    · exact False.elim (bad_shift_unique m B e (Classical.choose hx) j hB (by have := hcut _ hh.1; omega) (hcut _ hj) hlt hh.2 hb)
    · exact heq
    · exact False.elim (bad_shift_unique m B e j (Classical.choose hx) hB (by have := hcut _ hj; omega) (hcut _ hh.1) hgt hb hh.2)
  have he : ∃ j<n, j ∉ es.map bad := by
    by_cases h : ∃ j<n, j ∉ es.map bad
    · exact h
    · exfalso
      have hsub : List.range n ⊆ es.map bad := by
        intro j hj
        have hjn := List.mem_range.mp hj
        by_cases hjbad : j ∈ es.map bad
        · exact hjbad
        · exact False.elim (h ⟨j,hjn,hjbad⟩)
      have hle := (List.nodup_range (n:=n)).length_le_of_subset hsub
      simp [n] at hle
      omega
  rcases he with ⟨j,hj,hnot⟩
  refine ⟨j*B, by have := hcut _ hj; omega, hcut _ hj, ?_⟩
  intro e he
  by_cases hb : (e+j*B)%m ≤ m-B
  · exact hb
  · exact False.elim (hnot (List.mem_map.mpr ⟨e,he,hbad e j hj (by omega)⟩))

#print axioms rotation_congruence
#print axioms rotation_zero_of_gap
#print axioms exists_good_shift
end NeedleRotation
