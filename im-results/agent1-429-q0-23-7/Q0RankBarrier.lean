import Q0MacroCore
import Lean

/-! Exact signed rank-window reduction. Words are chronological; the earliest
    digit is the least significant radix-16 digit. -/
namespace BB429Q0Macro.RankBarrier
open BB429Q0Macro
set_option maxHeartbeats 4000000

def D : List Digit → Int
  | [] => 0
  | d::w => (digit d : Int) + 16 * D w

def L : List Digit → Nat
  | [] => 0
  | d::w => cost d + L w

def E : List Digit → Int
  | [] => 0
  | d::w => (offset d : Int) - (digit d : Int) * (L (d::w) : Int) + 16 * E w

def M (w : List Digit) : Int := 16 ^ w.length

private theorem M_pos (w : List Digit) : 0 < M w := by
  unfold M
  exact Int.pow_pos (by decide)

private theorem M_cons (d : Digit) (w : List Digit) : M (d::w) = 16*M w := by
  simp [M,Int.pow_succ,Int.mul_comm]

private theorem D_snoc (w : List Digit) (d : Digit) :
    D (w++[d]) = D w + digit d * M w := by
  induction w with
  | nil => simp [D,M]
  | cons r w ih =>
    simp only [List.cons_append,D,ih,M_cons]
    grind

private theorem L_snoc (w : List Digit) (d : Digit) : L (w++[d]) = L w+cost d := by
  induction w with
  | nil => simp [L]
  | cons r w ih => simp only [List.cons_append,L,ih]; omega

private theorem E_snoc (w : List Digit) (d : Digit) :
    E (w++[d]) = E w - cost d * D w +
      ((offset d : Int) - digit d * cost d) * M w := by
  induction w with
  | nil => simp [E,L,D,M]
  | cons r w ih =>
    simp only [List.cons_append,E,L,L_snoc,Int.natCast_add,D,ih,M_cons]
    grind

private theorem D_range (w : List Digit) : 0 ≤ D w ∧ 3*D w < M w := by
  induction w with
  | nil => decide
  | cons d w ih =>
    rw [M_cons,D]
    cases d <;> simp [digit] <;> omega

private theorem E_bounds_snoc (w : List Digit) (d : Digit)
    (h : -M w < 15*E w ∧ 15*E w < 2*M w) :
    -M (w++[d]) < 15*E (w++[d]) ∧ 15*E (w++[d]) < 2*M (w++[d]) := by
  have hD := D_range w
  have hM : M (w++[d]) = 16*M w := by
    simp [M,List.length_append,Int.pow_succ,Int.mul_comm]
  rw [E_snoc,hM]
  cases d <;> simp [digit,cost,offset] <;> omega

theorem E_bounds (w : List Digit) : -M w < 15*E w ∧ 15*E w < 2*M w := by
  have aux : ∀ v : List Digit, -M v.reverse < 15*E v.reverse ∧ 15*E v.reverse < 2*M v.reverse := by
    intro v
    induction v with
    | nil => decide
    | cons d v ih => simpa only [List.reverse_cons] using E_bounds_snoc v.reverse d ih
  simpa using aux w.reverse

/-- Exact labelled natural-valued execution of the already accepted graph. -/
inductive Trace : List Digit → Nat → Nat → Nat → Nat → Prop where
  | nil (p y : Nat) : Trace [] p y p y
  | cons (d : Digit) {w : List Digit} {p y P Y : Nat}
      (h : num d p y % 16 = 0)
      (tail : Trace w (nextP d p) (nextY d p y) P Y) : Trace (d::w) p y P Y

theorem trace_of_path {n p y : Nat} (h : Path n p y) :
    ∃ w P Y, w.length=n ∧ Trace w p y P Y := by
  induction h with
  | nil p y => exact ⟨[],p,y,rfl,.nil p y⟩
  | cons d h tail ih =>
    obtain ⟨w,P,Y,hw,ht⟩ := ih
    exact ⟨d::w,P,Y,by simp [hw],.cons d h ht⟩

theorem path_of_trace {w : List Digit} {p y P Y : Nat} (h : Trace w p y P Y) :
    Path w.length p y := by
  induction h with
  | nil => exact .nil ..
  | cons d h tail ih => exact .cons d h ih

theorem trace_formula {w : List Digit} {p y P Y : Nat} (h : Trace w p y P Y) :
    P=p+L w ∧ M w * Y = (y : Int)+D w * P+E w := by
  induction h with
  | nil p y => simp [L,M,D,E]
  | @cons d w p y P Y hd ht ih =>
    obtain ⟨hP,hY⟩ := ih
    have hnum : 16*nextY d p y = num d p y := by
      have h := Nat.mod_add_div (num d p y) 16
      unfold nextY
      omega
    have hnumI : (16 : Int)*(nextY d p y : Int) = (y : Int) + digit d * p + offset d := by
      unfold num at hnum
      exact_mod_cast hnum
    constructor
    · simp only [L,nextP] at *; omega
    · rw [M_cons,D,E,L]
      have hP' : (P : Int) = (p : Int)+cost d+L w := by
        unfold nextP at hP
        exact_mod_cast hP
      grind


/-- Endpoint formula is sufficient as well as necessary: exact integrality at
    the end of a chronological word forces every preceding division. -/
theorem trace_of_formula (w : List Digit) (p y P Y : Nat)
    (hP : P=p+L w) (hY : M w*Y=(y:Int)+D w*P+E w) : Trace w p y P Y := by
  induction w generalizing p y with
  | nil =>
    simp [L,M,D,E] at hP hY
    subst P
    have h : Y=y := by omega
    subst Y
    exact .nil ..
  | cons d w ih =>
    rw [M_cons,D,E,L] at hY
    have hpI : (P:Int)=(p:Int)+cost d+L w := by
      simp only [L] at hP
      exact_mod_cast (show P=p+cost d+L w by omega)
    have hnumI : ((num d p y : Nat) : Int) = (y:Int)+digit d*p+offset d := by
      simp [num,Int.natCast_add,Int.natCast_mul]
    have hnum : ((num d p y : Nat) : Int) = 16*(M w*Y-D w*P-E w) := by grind
    have hdiv : num d p y%16=0 := by omega
    have hnext : (nextY d p y : Int)=M w*Y-D w*P-E w := by
      unfold nextY
      omega
    apply Trace.cons d hdiv
    apply ih
    · simp [L,nextP] at *; omega
    · omega

private theorem trace_interior {w : List Digit} {p y P Y : Nat}
    (h : Trace w p y P Y) (hy : 0<y) (hc : 3*y<p) : 0<Y ∧ 3*Y<P := by
  induction h with
  | nil => exact ⟨hy,hc⟩
  | cons d hd tail ih =>
    obtain ⟨h1,h2⟩ := interior_step d _ _ hy hc hd
    exact ih h1 h2

/-- At rank a*16^k+b, any strict-interior k-step past forces an exact
    restricted-digit representation with a correction in [0,(a+b)/3]. -/
theorem near_power {w : List Digit} {p y P Y a b : Nat}
    (h : Trace w p y P Y) (hy : 0<y) (hc : 3*y<p)
    (hP : (P:Int)=(a:Int)*M w+b) :
    ∃ e : Nat, 3*e≤a+b ∧ (Y:Int)=(a:Int)*D w+e := by
  obtain ⟨hRank,hFormula⟩ := trace_formula h
  have hD := D_range w
  have hE := E_bounds w
  have hM := M_pos w
  let z : Int := (Y:Int)-(a:Int)*D w
  have hz : M w*z=(y:Int)+(b:Int)*D w+E w := by dsimp [z]; grind
  have hbD : 0≤(b:Int)*D w := Int.mul_nonneg (by omega) hD.1
  have hlow : 0≤z := by
    by_cases hneg : 0≤z
    · exact hneg
    · have hneg' : z≤ -1 := by omega
      have hm := Int.mul_le_mul_of_nonneg_left hneg' (show 0≤M w by omega)
      omega
  have hpI : (P:Int)=(p:Int)+L w := by exact_mod_cast hRank
  have hDmul : (b:Int)*(3*D w+1)≤(b:Int)*M w :=
    Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  have hsum : 3*((y:Int)+(b:Int)*D w)≤((a:Int)+b)*M w := by grind
  have hhi : 3*z≤(a:Int)+b := by
    by_cases hneg : 3*z≤(a:Int)+b
    · exact hneg
    · have hneg' : (a:Int)+b+1≤3*z := by omega
      have hm := Int.mul_le_mul_of_nonneg_left hneg' (show 0≤M w by omega)
      have hx : M w*(3*z)=3*(M w*z) := by grind
      have ha : M w*((a:Int)+b+1)=((a:Int)+b)*M w+M w := by grind
      omega
  refine ⟨z.toNat,?_,?_⟩ <;> omega

def Dn : List Digit → Nat
  | [] => 0
  | d::w => digit d+16*Dn w

theorem Dn_cast (w : List Digit) : (Dn w:Int)=D w := by
  induction w with
  | nil => rfl
  | cons d w ih => simp [Dn,D,Int.natCast_add,Int.natCast_mul,ih]

private theorem Dn_snoc (w : List Digit) (d : Digit) :
    Dn (w++[d]) = Dn w+digit d*16^w.length := by
  have h := D_snoc w d
  rw [←Dn_cast,←Dn_cast] at h
  unfold M at h
  exact_mod_cast h

/-- The small carry machine reads the preceding word, one digit per future
    macro step. Its rank is the offset from a*16^k. -/
def carryNum (a q e : Nat) (r d : Digit) := e+a*digit r+digit d*q+offset d

def carryY (a q e : Nat) (r d : Digit) := carryNum a q e r d/16

inductive Carry (a : Nat) : List Digit → List Digit → Nat → Nat → Nat → Nat → Prop where
  | nil (q e : Nat) : Carry a [] [] q e q e
  | cons (r d : Digit) {w v : List Digit} {q e Q F : Nat}
      (h : carryNum a q e r d%16=0)
      (tail : Carry a w v (q+cost d) (carryY a q e r d) Q F) :
      Carry a (r::w) (d::v) q e Q F

theorem carry_step_bound (a q e : Nat) (r d : Digit)
    (he : 3*e≤q+a) (h : carryNum a q e r d%16=0) :
    3*carryY a q e r d≤q+cost d+a := by
  have hdiv := Nat.mod_add_div (carryNum a q e r d) 16
  unfold carryY
  cases r <;> cases d <;> simp [carryNum,digit,cost,offset] at * <;> omega

private theorem cost_range (d : Digit) : 3≤cost d ∧ cost d≤6 := by cases d <;> decide

theorem carry_bounds {a q e Q F : Nat} {w v : List Digit}
    (h : Carry a w v q e Q F) (he : 3*e≤q+a) :
    w.length=v.length ∧ q+3*v.length≤Q ∧ Q≤q+6*v.length ∧ 3*F≤Q+a := by
  induction h with
  | nil => simp; exact he
  | cons r d hd tail ih =>
    have hb := carry_step_bound a _ _ r d he hd
    obtain ⟨h1,h2,h3,h4⟩ := ih hb
    have hcost := cost_range d
    simp only [List.length_cons]
    omega

/-- A single rolling-word identity. The carry division is equivalent to
    the true macro division, and all high-word arithmetic cancels exactly. -/
theorem rolling_num (a q e : Nat) (r d : Digit) (w : List Digit) :
    num d (a*16^(r::w).length+q) (a*Dn (r::w)+e) =
      16*(a*Dn (w++[d]))+carryNum a q e r d := by
  rw [Dn_snoc]
  simp only [num,Dn,List.length_cons,Nat.pow_succ,carryNum]
  grind

theorem rolling_div_iff (a q e : Nat) (r d : Digit) (w : List Digit) :
    num d (a*16^(r::w).length+q) (a*Dn (r::w)+e)%16=0 ↔
      carryNum a q e r d%16=0 := by
  rw [rolling_num]
  omega

theorem rolling_y (a q e : Nat) (r d : Digit) (w : List Digit) :
    nextY d (a*16^(r::w).length+q) (a*Dn (r::w)+e) =
      a*Dn (w++[d])+carryY a q e r d := by
  unfold nextY carryY
  rw [rolling_num]
  omega

private theorem rolling_rank (a q : Nat) (r d : Digit) (w pre : List Digit) :
    nextP d (a*16^((r::w)++pre).length+q) =
      a*16^(w++(pre++[d])).length+(q+cost d) := by
  have hlen : ((r::w)++pre).length=(w++(pre++[d])).length := by simp; omega
  rw [hlen]
  unfold nextP
  omega

/-- Any carry trace reconstructs the actual signed graph exactly. -/
theorem trace_of_carry {a q e Q F : Nat} {w v : List Digit}
    (h : Carry a w v q e Q F) (pre : List Digit) :
    Trace v (a*16^(w++pre).length+q) (a*Dn (w++pre)+e)
      (a*16^(w++pre).length+Q) (a*Dn (pre++v)+F) := by
  induction h generalizing pre with
  | nil q e => simpa using Trace.nil (a*16^pre.length+q) (a*Dn pre+e)
  | @cons r d w v q e Q F hd tail ih =>
    have hdiv := (rolling_div_iff a q e r d (w++pre)).2 hd
    apply Trace.cons d hdiv
    change Trace v (nextP d (a*16^((r::w)++pre).length+q)) _ _ _
    rw [rolling_rank a q r d w pre]
    rw [rolling_y]
    have hlen : (w++(pre++[d])).length=((r::w)++pre).length := by simp; omega
    have ht := ih (pre++[d])
    rw [hlen] at ht
    rw [hlen]
    simpa only [List.append_assoc,List.singleton_append] using ht

/-- Conversely every true k-step suffix through the near-power rank is
    represented by the small carry recurrence. -/
theorem carry_of_trace (a q e : Nat) (w v pre : List Digit) (P Y : Nat)
    (hlen : w.length=v.length)
    (h : Trace v (a*16^(w++pre).length+q) (a*Dn (w++pre)+e) P Y) :
    ∃ Q F, Carry a w v q e Q F ∧ P=a*16^(w++pre).length+Q ∧ Y=a*Dn (pre++v)+F := by
  induction w generalizing v pre q e P Y with
  | nil =>
    have hv : v=[] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
    subst v
    cases h
    exact ⟨q,e,.nil q e,rfl,by simp⟩
  | cons r w ih =>
    cases v with
    | nil => simp at hlen
    | cons d v =>
      simp only [List.length_cons] at hlen
      cases h with
      | cons d hd tail =>
        have hd' := (rolling_div_iff a q e r d (w++pre)).1 hd
        have hr := rolling_rank a q r d w pre
        have hy := rolling_y a q e r d (w++pre)
        rw [hr] at tail
        change Trace v _ (nextY d (a*16^(r::(w++pre)).length+q) (a*Dn (r::(w++pre))+e)) P Y at tail
        rw [hy] at tail
        rw [List.append_assoc] at tail
        obtain ⟨Q,F,hc,hp,hy'⟩ := ih (q+cost d) (carryY a q e r d) v (pre++[d]) P Y (by omega) tail
        refine ⟨Q,F,.cons r d hd' hc,?_,?_⟩
        · have hlen' : (w++(pre++[d])).length=((r::w)++pre).length := by simp; omega
          rw [hp,hlen']
        · simpa only [List.append_assoc,List.singleton_append] using hy'


/-- A k-step strict-interior past followed by k further steps at a specified
    near-power rank. -/
def Cross (a b k : Nat) : Prop :=
  ∃ (w v : List Digit) (p y Y P2 Y2 : Nat),
    w.length=k ∧ v.length=k ∧ 0<y ∧ 3*y<p ∧
    Trace w p y (a*16^k+b) Y ∧ Trace v (a*16^k+b) Y P2 Y2

def CarryCross (a b k : Nat) : Prop :=
  ∃ (w v : List Digit) (e q f : Nat),
    w.length=k ∧ v.length=k ∧ 3*e≤a+b ∧
    0 < M w*e-b*D w-E w ∧
    3*(M w*e-b*D w-E w)<(a:Int)*M w+b-L w ∧
    Carry a w v b e q f

/-- The crossing problem is exactly a finite-width carry strip and an
    initial-cone test. No root-reachability claim is implicit. -/
theorem crossing_iff (a b k : Nat) : Cross a b k ↔ CarryCross a b k := by
  constructor
  · rintro ⟨w,v,p,y,Y,P2,Y2,hw,hv,hy,hc,ht,hs⟩
    have hP : ((a*16^k+b : Nat):Int)=(a:Int)*M w+b := by
      simp [M,hw,Int.natCast_add,Int.natCast_mul,Int.natCast_pow]
    obtain ⟨e,he,hY⟩ := near_power ht hy hc hP
    have hY' : Y=a*Dn w+e := by rw [←Dn_cast] at hY; exact_mod_cast hY
    rw [hY',←hw] at hs
    have hs' : Trace v (a*16^(w++[]).length+b) (a*Dn (w++[])+e) P2 Y2 := by simpa using hs
    obtain ⟨q,f,hcarry,_,_⟩ := carry_of_trace a b e w v [] P2 Y2 (by omega) hs'
    obtain ⟨hp,hf⟩ := trace_formula ht
    have hp' : ((a*16^k+b : Nat):Int)=(p:Int)+L w := by exact_mod_cast hp
    have hy' : (y:Int)=M w*e-b*D w-E w := by grind
    refine ⟨w,v,e,q,f,hw,hv,he,?_,?_,hcarry⟩
    · omega
    · omega
  · rintro ⟨w,v,e,q,f,hw,hv,he,hy,hc,hcarry⟩
    let pI : Int := (a:Int)*M w+b-L w
    let yI : Int := M w*e-b*D w-E w
    have hp : 0≤pI := by dsimp [pI,yI] at *; omega
    have hyI : 0≤yI := by dsimp [yI]; omega
    let p := pI.toNat
    let y := yI.toNat
    have hp' : (p:Int)=pI := by simp [p,Int.toNat_of_nonneg hp]
    have hy' : (y:Int)=yI := by simp [y,Int.toNat_of_nonneg hyI]
    have hP : ((a*16^k+b : Nat):Int)=(a:Int)*M w+b := by
      simp [M,hw,Int.natCast_add,Int.natCast_mul,Int.natCast_pow]
    have hRank : a*16^k+b=p+L w := by dsimp [pI] at hp'; omega
    have hDn := Dn_cast w
    have hY : M w*(a*Dn w+e : Nat)=(y:Int)+D w*(a*16^k+b : Nat)+E w := by
      simp only [Int.natCast_add,Int.natCast_mul]
      dsimp [yI] at hy'
      grind
    have ht := trace_of_formula w p y (a*16^k+b) (a*Dn w+e) hRank hY
    have hs := trace_of_carry hcarry []
    simp [hw] at hs
    refine ⟨w,v,p,y,a*Dn w+e,a*16^k+q,a*Dn v+f,hw,hv,?_,?_,ht,hs⟩
    · dsimp [yI] at hy'; omega
    · dsimp [pI,yI] at hp' hy'; omega

#print axioms trace_of_formula
#print axioms near_power
#print axioms E_bounds
#print axioms carry_bounds
#print axioms rolling_div_iff
#print axioms crossing_iff
end BB429Q0Macro.RankBarrier
