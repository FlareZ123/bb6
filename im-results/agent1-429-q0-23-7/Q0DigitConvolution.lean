import Lean

namespace BB429Q0Macro.DigitConvolution
set_option maxHeartbeats 8000000

abbrev History := Nat → Bool

def bit (b : Bool) : Nat := if b then 1 else 0

def push (d : Bool) (h : History) : History
  | 0 => d
  | n+1 => h n

/-- The most recent j binary choices, interpreted in radix four,
    with the most recent choice most significant. -/
def value (h : History) : Nat → Nat
  | 0 => 0
  | j+1 => 4*value h j+bit (h j)

theorem bit_le (b : Bool) : bit b≤1 := by cases b <;> decide

theorem value_bound (h : History) (j : Nat) : 3*value h j<4^j := by
  induction j with
  | zero => simp [value]
  | succ j ih =>
    have hb := bit_le (h j)
    rw [value,Nat.pow_succ]
    omega

theorem value_extend (h : History) (j m : Nat) :
    value h (j+m)=4^m*value h j+value (fun i => h (j+i)) m := by
  induction m with
  | zero => simp [value]
  | succ m ih =>
    rw [Nat.add_succ,value,ih,value,Nat.pow_succ]
    grind

theorem value_push (h : History) (d : Bool) (j : Nat) :
    value (push d h) (j+1)=bit d*4^j+value h j := by
  induction j with
  | zero => simp [value,push]
  | succ j ih =>
    rw [value,ih,value,Nat.pow_succ]
    simp [push]
    grind

theorem value_roll (h : History) (d : Bool) (j : Nat) :
    4*value (push d h) j+bit (push d h j)=value h j+bit d*4^j := by
  cases j with
  | zero => simp [value,push]
  | succ j => rw [value_push,value,Nat.pow_succ]; simp [push]; grind

/-- Scaled prefix approximation: the omitted suffix contributes less
    than one third of the modulus, independent of the rank digits. -/
theorem prefix_approx (h : History) (j k : Nat) (hj : j≤k) :
    4^k*value h j≤4^j*value h k ∧
    3*(4^j*value h k)≤3*(4^k*value h j)+4^k := by
  let m := k-j
  have hk : k=j+m := by omega
  have hv := value_extend h j m
  have hb := value_bound (fun i => h (j+i)) m
  have hpow : 4^k=4^j*4^m := by rw [hk,Nat.pow_add]
  have hv' : value h k=4^m*value h j+value (fun i => h (j+i)) m := by rw [hk,hv]
  have he : 4^j*value h k=4^k*value h j+4^j*value (fun i => h (j+i)) m := by rw [hv',hpow]; grind
  have hmul := Nat.mul_le_mul_left (4^j) (show 3*value (fun i => h (j+i)) m≤4^m by omega)
  have hmul' : 3*(4^j*value (fun i => h (j+i)) m)≤4^k := by rw [hpow]; simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hmul
  omega

/-- Little-endian radix-four rank digits. -/
def rankValue : List Nat → Nat
  | [] => 0
  | a::v => a+4*rankValue v

def digitSum : List Nat → Nat
  | [] => 0
  | a::v => a+digitSum v

/-- Convolution of rank digits with all suffixes of a chronological
    history. This replaces a large height by a logarithmic residue. -/
def convFrom (h : History) (j : Nat) : List Nat → Nat
  | [] => 0
  | a::v => a*value h j+convFrom h (j+1) v

def conv (h : History) (ds : List Nat) : Nat := convFrom h 0 ds

def bitDotFrom (h : History) (j : Nat) : List Nat → Nat
  | [] => 0
  | a::v => a*bit (h j)+bitDotFrom h (j+1) v

def bitDot (h : History) (ds : List Nat) : Nat := bitDotFrom h 0 ds

theorem conv_roll_from (h : History) (d : Bool) (j : Nat) (ds : List Nat) :
    4*convFrom (push d h) j ds+bitDotFrom (push d h) j ds=
      convFrom h j ds+bit d*(4^j*rankValue ds) := by
  induction ds generalizing j with
  | nil => simp [convFrom,bitDotFrom,rankValue]
  | cons a ds ih =>
    simp only [convFrom,bitDotFrom,rankValue] at *
    have hr := value_roll h d j
    have hi := ih (j+1)
    rw [Nat.pow_succ] at hi
    grind

theorem conv_roll (h : History) (d : Bool) (ds : List Nat) :
    4*conv (push d h) ds+bitDot (push d h) ds=conv h ds+bit d*rankValue ds := by
  simpa [conv,bitDot] using conv_roll_from h d 0 ds

/-- A fixed-width radix-four addition with all outgoing carries recorded.
    The terminal carry is zero. -/
inductive Addition : Nat → List Nat → List Nat → List Nat → Prop where
  | nil : Addition 0 [] [] []
  | cons (c a b n : Nat) {v w cs : List Nat}
      (he : a+c=b+4*n) (hb : b<4) (ht : Addition n v w cs) :
      Addition c (a::v) (b::w) (n::cs)

theorem Addition.rank {c ds es cs} (h : Addition c ds es cs) :
    rankValue es=rankValue ds+c := by
  induction h with
  | nil => rfl
  | cons c a b n he hb ht ih => simp [rankValue,ih]; omega

theorem Addition.sum {c ds es cs} (h : Addition c ds es cs) :
    digitSum es+3*digitSum cs=digitSum ds+c := by
  induction h with
  | nil => rfl
  | cons c a b n he hb ht ih => simp [digitSum]; omega

theorem Addition.length {c ds es cs} (h : Addition c ds es cs) :
    es.length=ds.length ∧ cs.length=ds.length := by
  induction h with
  | nil => simp
  | cons c a b n he hb ht ih => simp [ih]

theorem Addition.digits {c ds es cs} (h : Addition c ds es cs) : ∀ x∈es, x<4 := by
  induction h with
  | nil => simp
  | cons c a b n he hb ht ih => simp; exact ⟨hb,ih⟩

theorem Addition.exists_of_bound (ds : List Nat) (c : Nat)
    (h : rankValue ds+c<4^ds.length) : ∃ es cs, Addition c ds es cs := by
  induction ds generalizing c with
  | nil =>
    simp [rankValue] at h
    have hc : c=0 := by omega
    subst c
    exact ⟨[],[],.nil⟩
  | cons a ds ih =>
    let b := (a+c)%4
    let n := (a+c)/4
    have he : a+c=b+4*n := by dsimp [b,n]; omega
    have hb : b<4 := by dsimp [b]; omega
    simp only [rankValue,List.length_cons,Nat.pow_succ] at h
    have hn : rankValue ds+n<4^ds.length := by omega
    obtain ⟨es,cs,ht⟩ := ih n hn
    exact ⟨b::es,n::cs,.cons c a b n he hb ht⟩

theorem Addition.conv_from {c ds es cs} (h : Addition c ds es cs) (w : History) (j : Nat) :
    convFrom w j es=convFrom w j ds+c*value w j+bitDotFrom w j cs := by
  induction h generalizing j with
  | nil => simp [convFrom,bitDotFrom]
  | cons c a b n he hb ht ih =>
    simp only [convFrom,bitDotFrom]
    rw [ih (j+1),value]
    grind

theorem Addition.conv {c ds es cs} (h : Addition c ds es cs) (w : History) :
    conv w es=conv w ds+bitDot w cs := by
  simpa [DigitConvolution.conv,bitDot,value] using h.conv_from w 0

theorem digits_exist (P n : Nat) (h : P<4^n) :
    ∃ ds : List Nat, ds.length=n ∧ rankValue ds=P ∧ ∀ d∈ds, d<4 := by
  induction n generalizing P with
  | zero =>
    have hp : P=0 := by simp at h; omega
    exact ⟨[],rfl,by simp [rankValue,hp],by simp⟩
  | succ n ih =>
    let a := P%4
    let Q := P/4
    have he : P=a+4*Q := by dsimp [a,Q]; omega
    have ha : a<4 := by dsimp [a]; omega
    rw [Nat.pow_succ] at h
    have hQ : Q<4^n := by omega
    obtain ⟨ds,hl,hr,hd⟩ := ih Q hQ
    refine ⟨a::ds,by simp [hl],by simp [rankValue,hr]; omega,?_⟩
    intro d hm
    simp at hm
    rcases hm with rfl|hm
    · exact ha
    · exact hd d hm

/-- The convolution omits at most digitSum/3 of the normalized
    rank-times-history product. -/
theorem conv_approx_from (h : History) (j k : Nat) (ds : List Nat)
    (hj : j+ds.length≤k+1) :
    4^k*convFrom h j ds≤(4^j*rankValue ds)*value h k ∧
    3*((4^j*rankValue ds)*value h k)≤3*(4^k*convFrom h j ds)+4^k*digitSum ds := by
  induction ds generalizing j with
  | nil => simp [convFrom,rankValue,digitSum]
  | cons a ds ih =>
    have hj' : j≤k := by simp at hj; omega
    have htail : j+1+ds.length≤k+1 := by simp at hj; omega
    obtain ⟨hlo,hhi⟩ := prefix_approx h j k hj'
    obtain ⟨tlo,thi⟩ := ih (j+1) htail
    have alo := Nat.mul_le_mul_left a hlo
    have ahi := Nat.mul_le_mul_left a hhi
    rw [Nat.pow_succ] at tlo thi
    simp only [convFrom,rankValue,digitSum]
    constructor
    · calc
        4^k*(a*value h j+convFrom h (j+1) ds)
          = a*(4^k*value h j)+4^k*convFrom h (j+1) ds := by grind
        _ ≤ a*(4^j*value h k)+(4^j*4*rankValue ds)*value h k := Nat.add_le_add alo tlo
        _ = (4^j*(a+4*rankValue ds))*value h k := by grind
    · calc
        3*((4^j*(a+4*rankValue ds))*value h k)
          = a*(3*(4^j*value h k))+3*((4^j*4*rankValue ds)*value h k) := by grind
        _ ≤ a*(3*(4^k*value h j)+4^k)+(3*(4^k*convFrom h (j+1) ds)+4^k*digitSum ds) := Nat.add_le_add ahi thi
        _ = 3*(4^k*(a*value h j+convFrom h (j+1) ds))+4^k*(a+digitSum ds) := by grind

theorem conv_approx (h : History) (k : Nat) (ds : List Nat) (hj : ds.length≤k+1) :
    4^k*conv h ds≤rankValue ds*value h k ∧
    3*(rankValue ds*value h k)≤3*(4^k*conv h ds)+4^k*digitSum ds := by
  simpa [conv] using conv_approx_from h 0 k ds (by omega)

/-- With k actual past half-steps and rank at most 4^k, the remaining
    height carry is bounded by the radix-four digit sum, not the rank. -/
theorem residual_bound (h : History) (k : Nat) (ds : List Nat) (y Y : Nat) (E : Int)
    (hj : ds.length≤k+1) (hp : rankValue ds≤4^k)
    (hy : 0<y) (hc : 3*y<rankValue ds)
    (hElo : -(4:Int)^k<E) (hEhi : 15*E<13*(4:Int)^k)
    (hf : (4:Int)^k*(Y:Int)=(y:Int)+(rankValue ds:Int)*(value h k:Int)+E) :
    let e : Int := (Y:Int)-conv h ds
    0≤e ∧ 3*e≤(digitSum ds:Int)+3 := by
  dsimp
  obtain ⟨hlo,hhi⟩ := conv_approx h k ds hj
  have hpos : 0<(4:Int)^k := Int.pow_pos (by decide)
  have hloI : (4:Int)^k*(conv h ds:Int)≤(rankValue ds:Int)*(value h k:Int) := by exact_mod_cast hlo
  have hhiI : 3*((rankValue ds:Int)*(value h k:Int))≤3*((4:Int)^k*(conv h ds:Int))+(4:Int)^k*(digitSum ds:Int) := by exact_mod_cast hhi
  have hpI : (rankValue ds:Int)≤(4:Int)^k := by exact_mod_cast hp
  have hyI : 0<(y:Int) := by omega
  have hcI : 3*(y:Int)<(rankValue ds:Int) := by exact_mod_cast hc
  let e : Int := (Y:Int)-conv h ds
  have he : (4:Int)^k*e=(y:Int)+((rankValue ds:Int)*(value h k:Int)-(4:Int)^k*(conv h ds:Int))+E := by dsimp [e]; grind
  have hlow : (4:Int)^k*(-1)<(4:Int)^k*e := by simp; omega
  have hhigh : (4:Int)^k*(45*e)<(4:Int)^k*(15*(digitSum ds:Int)+54) := by
    rw [Int.mul_add,show (4:Int)^k*(45*e)=45*((4:Int)^k*e) by grind,he]
    rw [show (4:Int)^k*(15*(digitSum ds:Int))=15*((4:Int)^k*(digitSum ds:Int)) by grind]
    omega
  have hlow' := Int.lt_of_mul_lt_mul_left hlow (by omega : 0≤(4:Int)^k)
  have hhigh' := Int.lt_of_mul_lt_mul_left hhigh (by omega : 0≤(4:Int)^k)
  change 0≤e ∧ 3*e≤(digitSum ds:Int)+3
  omega

/-- Exact small-residue transition. Only the rank digits, the shifted
    history bits, and the ordinary radix carry digits enter. -/
theorem residual_roll (h : History) (d : Bool) {ds es cs : List Nat} {l : Nat}
    (ha : Addition l ds es cs) (y Y c : Nat)
    (ht : 4*Y=y+bit d*rankValue ds+c) :
    4*((Y:Int)-conv (push d h) es)+4*(bitDot (push d h) cs:Int)=
      ((y:Int)-conv h ds)+(c:Int)+bitDot (push d h) ds := by
  have hroll := conv_roll h d ds
  have hadd := ha.conv (push d h)
  have hrollI : 4*(conv (push d h) ds:Int)+(bitDot (push d h) ds:Int)=(conv h ds:Int)+(bit d:Int)*rankValue ds := by exact_mod_cast hroll
  have haddI : (conv (push d h) es:Int)=(conv (push d h) ds:Int)+bitDot (push d h) cs := by exact_mod_cast hadd
  have htI : 4*(Y:Int)=(y:Int)+(bit d:Int)*rankValue ds+c := by exact_mod_cast ht
  omega

theorem residual_reconstruct (h : History) (d : Bool) {ds es cs : List Nat} {l : Nat}
    (ha : Addition l ds es cs) (y Y c : Nat)
    (ht : 4*((Y:Int)-conv (push d h) es)+4*(bitDot (push d h) cs:Int)=
      ((y:Int)-conv h ds)+(c:Int)+bitDot (push d h) ds) :
    4*Y=y+bit d*rankValue ds+c := by
  have hroll := conv_roll h d ds
  have hadd := ha.conv (push d h)
  have hrollI : 4*(conv (push d h) ds:Int)+(bitDot (push d h) ds:Int)=(conv h ds:Int)+(bit d:Int)*rankValue ds := by exact_mod_cast hroll
  have haddI : (conv (push d h) es:Int)=(conv (push d h) ds:Int)+bitDot (push d h) cs := by exact_mod_cast hadd
  have he : 4*(Y:Int)=(y:Int)+(bit d:Int)*rankValue ds+c := by omega
  exact_mod_cast he

theorem digitSum_le (ds : List Nat) (hd : ∀ d∈ds, d<4) :
    digitSum ds≤3*ds.length := by
  induction ds with
  | nil => simp [digitSum]
  | cons d ds ih =>
    have h₁ := hd d (by simp)
    have h₂ := ih (by intro a ha; exact hd a (by simp [ha]))
    simp [digitSum]; omega

theorem complement_roll (h : History) (d : Bool) {ds es cs : List Nat} {l : Nat}
    (ha : Addition l ds es cs) (e E : Int) (c : Nat)
    (ht : 4*E+4*(bitDot (push d h) cs:Int)=e+(c:Int)+bitDot (push d h) ds) :
    4*((digitSum es:Int)-3*E) = (digitSum ds:Int)-3*e+
      3*((digitSum ds:Int)-bitDot (push d h) ds)+4*(l:Int)-3*(c:Int)-
      12*((digitSum cs:Int)-bitDot (push d h) cs) := by
  have hs : (digitSum es:Int)+3*(digitSum cs:Int)=(digitSum ds:Int)+l := by exact_mod_cast ha.sum
  omega

#print axioms conv_approx
#print axioms Addition.exists_of_bound
#print axioms residual_bound
#print axioms residual_roll
#print axioms residual_reconstruct
#print axioms digitSum_le
#print axioms complement_roll
end BB429Q0Macro.DigitConvolution
