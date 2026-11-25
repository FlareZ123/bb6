import Lean

namespace BB6.Agent12Dyadic

/-- Integer coordinates; the formulas extend continuously to Z₂. -/
structure Coord where
  l : Int
  h : Int
  o : Nat
  deriving Repr, DecidableEq

def encode (a k : Nat) : Coord :=
  ⟨(a/2:Nat)+1+(a%2:Nat), (a/2:Nat)+k, a%2⟩

def nextParity (r o : Nat) : Nat := (o+r+1)%2

def delta (r o : Nat) : Nat := (o+3*r+1-nextParity r o)/2

def affine (r : Nat) (s : Coord) : Coord :=
  let h := s.h+(delta r s.o:Nat)
  ⟨(2:Int)^r*s.l-h+1-(s.o:Nat),h,nextParity r s.o⟩

theorem encode_equations (a k : Nat) :
    (a:Int)=2*(encode a k).l-2-((encode a k).o:Nat) ∧
    (a:Int)+2*k=2*(encode a k).h+((encode a k).o:Nat) ∧
    (k:Int)=(encode a k).h-(encode a k).l+1+((encode a k).o:Nat) ∧
    (a:Int)+k=(encode a k).l+(encode a k).h-1 := by
  simp [encode]; omega

/-- A branch satisfying the exact ordinary affine equations in section
    coordinates is precisely the new critical IFS edge. -/
theorem affine_of_equations (a k x y r : Nat) (hr : 1≤r)
    (hm : x+2*y=a+2*k+3*r+1)
    (ha : 2^r*(a+2+a%2)=2*x+2*y+2*(a%2)) :
    affine r (encode a k)=encode x y := by
  have hpar : x%2=nextParity r (a%2) := by unfold nextParity; omega
  have hd : 2*delta r (a%2)+(x%2)=a%2+3*r+1 := by
    unfold delta
    rw [←hpar]
    have h : (a%2+3*r+1)%2=x%2 := by omega
    omega
  obtain ⟨hA,hM,_,_⟩ := encode_equations a k
  obtain ⟨hX,hN,_,hS⟩ := encode_equations x y
  have ho : (encode a k).o=a%2 := rfl
  have hop : (encode x y).o=x%2 := rfl
  have hHi : (encode x y).h=(encode a k).h+(delta r (a%2):Nat) := by
    rw [ho] at hM
    rw [hop] at hN
    omega
  have hAI : (2:Int)^r*((a:Int)+2+(a%2:Nat))=2*(x:Int)+2*y+2*(a%2:Nat) := by exact_mod_cast ha
  rw [ho] at hA
  have hB : (a:Int)+2+(a%2:Nat)=2*(encode a k).l := by omega
  rw [hB,show 2*(x:Int)+2*y=2*((x:Int)+y) by omega,hS] at hAI
  have hL : (encode x y).l=(2:Int)^r*(encode a k).l-(encode x y).h+1-(a%2:Nat) := by
    rw [show (2:Int)^r*(2*(encode a k).l)=2*((2:Int)^r*(encode a k).l) by ac_rfl] at hAI
    omega
  simp only [affine,ho,←hHi,←hL,←hpar,←hop]

/-- Compose in chronological order. Each nonempty word has odd mass
    coefficient q, since its last edge contributes the unit term. -/
def run : List Nat → Coord → Coord
  | [],s => s
  | r::rs,s => run rs (affine r s)

structure Coeff where
  p : Nat
  q : Int
  c : Int
  d : Nat
  o : Nat
  deriving Repr

def coeff : List Nat → Nat → Coeff
  | [],o => ⟨0,0,0,0,o⟩
  | r::rs,o =>
    let v := coeff rs (nextParity r o)
    ⟨r+v.p, (2:Int)^v.p+v.q,
      (2:Int)^v.p*(1-(o:Int))+(2:Int)^v.p*(v.d:Nat)+v.c,
      delta r o+v.d,v.o⟩

theorem run_formula (rs : List Nat) (s : Coord) :
    let v := coeff rs s.o
    let t := run rs s
    t.h=s.h+(v.d:Nat) ∧ t.o=v.o ∧
      t.l=(2:Int)^v.p*s.l-v.q*t.h+v.c := by
  induction rs generalizing s with
  | nil => simp [run,coeff]
  | cons r rs ih =>
    have h := ih (affine r s)
    simp only [run,coeff,affine] at h ⊢
    obtain ⟨hh,ho,hl⟩ := h
    refine ⟨by push_cast; omega,ho,?_⟩
    rw [hl,Int.pow_add]
    push_cast
    grind

theorem coeff_p (rs : List Nat) (o : Nat) : (coeff rs o).p=rs.sum := by
  induction rs generalizing o with
  | nil => rfl
  | cons r rs ih => simp [coeff,ih,List.sum_cons]

theorem coeff_q_odd (r : Nat) (rs : List Nat) (o : Nat)
    (h : ∀ v∈rs, 1≤v) : (coeff (r::rs) o).q%2=1 := by
  induction rs generalizing r o with
  | nil => simp [coeff]
  | cons t ts ih =>
    have ht := h t (by simp)
    have hs : ∀ v∈ts, 1≤v := by intro v hv; exact h v (by simp [hv])
    have hq := ih t (nextParity r o) hs
    have hp : 1≤(coeff (t::ts) (nextParity r o)).p := by
      simp [coeff]; omega
    have hpow : (2:Int)^((coeff (t::ts) (nextParity r o)).p)%2=0 := by
      obtain ⟨n,hn⟩ : ∃ n, (coeff (t::ts) (nextParity r o)).p=n+1 := ⟨(coeff (t::ts) (nextParity r o)).p-1,by omega⟩
      rw [hn,Int.pow_succ]; omega
    simp only [coeff] at hq hpow ⊢
    omega

/-- Sequence of increasing odd split positions, compatible at every
    earlier binary precision. No finite bound is put on its length. -/
def splitPos : Nat → Nat
  | 0 => 1
  | n+1 => splitPos n + 2^(splitPos n+1)

theorem splitPos_succ_gt (n : Nat) : splitPos n<splitPos (n+1) := by
  rw [splitPos]
  have h : 0<2^(splitPos n+1) := Nat.pow_pos (by decide)
  omega

theorem splitPos_mono (i n : Nat) (h : i≤n) : splitPos i≤splitPos n := by
  induction n with
  | zero =>
    have hi : i=0 := by omega
    subst i
    exact Nat.le_refl _
  | succ n ih =>
    by_cases hi : i=n+1
    · subst i; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (Nat.le_of_lt (splitPos_succ_gt n))

theorem splitPos_odd (n : Nat) : splitPos n%2=1 := by
  induction n with
  | zero => decide
  | succ n ih => rw [splitPos, Nat.pow_succ]; omega

theorem splitPos_div (i n : Nat) (h : i≤n) :
    2^(splitPos i+1)∣splitPos n-splitPos i := by
  induction n with
  | zero =>
    have hi : i=0 := by omega
    subst i
    simp
  | succ n ih =>
    by_cases hi : i=n+1
    · subst i; simp
    · have hin : i≤n := by omega
      have hm := splitPos_mono i n hin
      have hpow : 2^(splitPos i+1)∣2^(splitPos n+1) := Nat.pow_dvd_pow 2 (by omega)
      rw [splitPos, Nat.add_comm (splitPos n), Nat.add_sub_assoc hm]
      exact Nat.dvd_add hpow (ih hin)

theorem odd_delta (r o : Nat) (hr : r%2=1) (ho : o≤1) :
    nextParity r o=o ∧ 2*delta r o=3*r+1 := by
  have hp : nextParity r o=o := by unfold nextParity; omega
  refine ⟨hp,?_⟩
  unfold delta
  rw [hp]
  have h : (3*r+1)%2=0 := by omega
  omega

/-- For arbitrary n+1, the n+1 words [pᵢ,R-pᵢ] have the same
    shift R and mass increment, and their image residues coincide on
    the cylinder H'=3-o mod 2^(pₙ). -/
theorem many_splits (i n o : Nat) (hi : i≤n) (ho : o≤1)
    (s : Coord) (hso : s.o=o)
    (hH : (2:Int)^splitPos n ∣ s.h+((3*(splitPos n+1)+2)/2:Nat)-3+(o:Nat)) :
    let p := splitPos i
    let R := splitPos n+1
    let q := R-p
    let t := run [p,q] s
    p%2=1 ∧ q%2=1 ∧ p+q=R ∧
      t.h=s.h+((3*R+2)/2:Nat) ∧ t.o=o ∧
      (2:Int)^R ∣ t.l+t.h-1+(o:Nat) := by
  let p := splitPos i
  let R := splitPos n+1
  let q := R-p
  have hmono := splitPos_mono i n hi
  have hp : p%2=1 := splitPos_odd i
  have hn := splitPos_odd n
  have hq : q%2=1 := by dsimp [q,R,p] at *; omega
  have hR : p+q=R := by dsimp [q,R,p]; omega
  have ⟨hpo,hpd⟩ := odd_delta p o hp ho
  have ⟨hqo,hqd⟩ := odd_delta q o hq ho
  have hd : delta p o+delta q o=(3*R+2)/2 := by omega
  let H := s.h+((3*R+2)/2:Nat)
  have hh : H=s.h+(delta p o:Nat)+(delta q o:Nat) := by dsimp [H]; omega
  have hdiv : (2:Int)^p ∣ H-3+(o:Nat) := by
    have hdiv2 : (2:Int)^p ∣ (2:Int)^splitPos n := by
      refine ⟨(2:Int)^(splitPos n-p),?_⟩
      rw [←Int.pow_add,show p+(splitPos n-p)=splitPos n by omega]
    exact Int.dvd_trans hdiv2 hH
  obtain ⟨v,hv⟩ := splitPos_div i n hi
  have hq' : q=1+2^(p+1)*v := by dsimp [q,R,p] at *; omega
  have hdq : (delta q o:Int)=2+3*(2:Int)^p*v := by
    have hqI : (q:Int)=1+(2:Int)^(p+1)*v := by exact_mod_cast hq'
    rw [Int.pow_succ] at hqI
    have hdI : 2*(delta q o:Int)=3*(q:Int)+1 := by exact_mod_cast hqd
    rw [hqI] at hdI
    grind
  have hdiv' : (2:Int)^p ∣ H-(delta q o:Nat)-1+(o:Nat) := by
    obtain ⟨j,hj⟩ := hdiv
    refine ⟨j-3*(v:Nat),?_⟩
    rw [hdq,Int.mul_sub]
    grind
  change p%2=1 ∧ q%2=1 ∧ p+q=R ∧
      (run [p,q] s).h=H ∧ (run [p,q] s).o=o ∧
      (2:Int)^R ∣ (run [p,q] s).l+(run [p,q] s).h-1+(o:Nat)
  refine ⟨hp,hq,hR,?_,?_,?_⟩
  · simp only [run,affine,hso,hpo,hqo]
    exact hh.symm
  · simp only [run,affine,hso,hpo,hqo]
  · simp only [run,affine,hso,hpo,hqo]
    obtain ⟨j,hj⟩ := hdiv'
    have hmid : s.h+(delta p o:Nat)-1+(o:Nat)=(2:Int)^p*j := by omega
    -- show the left coordinate after two edges differs from the common
    -- center by 2^R times (initial L minus j).
    refine ⟨s.l-j,?_⟩
    rw [←hR,Int.pow_add]
    grind

#print axioms affine_of_equations
#print axioms run_formula
#print axioms coeff_q_odd
#print axioms splitPos_div
#print axioms many_splits
end BB6.Agent12Dyadic
