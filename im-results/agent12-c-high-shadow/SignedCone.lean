import HighShadowArithmetic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent12SignedCone
open BB6.Agent12HighShadow

structure Offset where
  x : Int
  y : Int
  deriving Repr, DecidableEq

def p (b : Nat) : Int := (2:Int)^b
private theorem ppos (b : Nat) : 0<p b := Int.pow_pos (by decide)
private theorem pcast (b : Nat) : p b = (↑((2:Nat)^b):Int) := by simp [p]
private theorem psplit (b r : Nat) (h : r≤b) : p b=p (b-r)*p r := by
  unfold p
  rw [←Int.pow_add]
  congr 1
  omega
private theorem psucc (b : Nat) : p (b+1)=2*p b := by
  unfold p
  rw [Int.pow_succ,Int.mul_comm]
private theorem pdvd (b r : Nat) (h : r≤b) : p r∣p b := by
  refine ⟨p (b-r),?_⟩
  rw [psplit b r h,Int.mul_comm]

/-- The exact large part is not computed. The left coefficient may be
    zero only when its signed offset is itself above the source boundary. -/
def Rep (b x y : Nat) (s : Offset) : Prop :=
  ∃ A B : Int, 0≤A ∧ 1≤B ∧ (1≤A ∨ 5<s.x) ∧
    (x:Int)=p b*A+s.x ∧ (y:Int)=p b*B+s.y

def small (b : Nat) (s : Offset) : Bool :=
  decide ((2*(s.x.natAbs+s.y.natAbs+8)).log2<b)
def oddPart (s : Offset) : Int := (s.x+s.y)%2
def rounded (s : Offset) : Int := s.x+s.y+oddPart s
def mass (s : Offset) : Int := s.x+2*s.y
def bad (s : Offset) : Bool := decide (s.y%2=1 ∧ ((s.x+s.y)%4=1 ∨ (s.x+s.y)%4=2))

def v2Aux : Nat → Nat → Nat
  | 0,_ => 0
  | f+1,n => if n%2=0 then 1+v2Aux f (n/2) else 0

def val (s : Offset) : Nat := v2Aux ((rounded s).natAbs.log2+1) (rounded s).natAbs
def validVal (b : Nat) (s : Offset) : Bool :=
  decide (val s+1≤b ∧ rounded s % p (val s+1)=p (val s))
def dir (s : Offset) : Offset := ⟨s.x+s.y-2,(s.y-2)/2⟩
def dirValid (s t : Offset) : Bool := decide (t.x+2=s.x+s.y ∧ 2*t.y+2=s.y)
def hi (s : Offset) (n : Nat) : Offset :=
  let a := rounded s / p (n+1)-2-oddPart s
  ⟨a,(mass s-a-7-3*(n:Int))/2⟩
def hiValid (s t : Offset) (n : Nat) : Bool := decide (
  p (n+1)*(t.x+2+oddPart s)=rounded s ∧
  2*t.y+t.x+7+3*(n:Int)=mass s)
def depthOK (s : Offset) (n : Nat) : Bool :=
  decide (n+2≤val s ∧ (n:Int)%2=(s.x+1+oddPart s)%2)

def check : Nat → Nat → Offset → Bool
  | 0,b,s => small b s && bad s
  | f+1,b,s => small b s && (bad s || (validVal b s &&
    (if s.y%2=0 then dirValid s (dir s) && check f (b-1) (dir s) else true) &&
    (List.range (val s+1)).all (fun n => if depthOK s n then
      hiValid s (hi s n) n && check f (b-(n+2)) (hi s n) else true)))

private theorem abs_lower (x : Int) : -(x.natAbs:Int)≤x := by
  by_cases h : 0≤x
  · omega
  · rw [Int.eq_neg_natAbs_of_nonpos (by omega : x≤0)]
    simp

private theorem small_facts (b : Nat) (s : Offset) (h : small b s=true) :
    2≤b ∧ 2*((s.x.natAbs:Int)+(s.y.natAbs:Int)+8)<p b := by
  have hh : (2*(s.x.natAbs+s.y.natAbs+8)).log2<b := of_decide_eq_true h
  have hn := (Nat.log2_lt (by omega : 2*(s.x.natAbs+s.y.natAbs+8)≠0)).mp hh
  have hb : 2≤b := by
    by_cases hc : 2≤b
    · exact hc
    · have hle : (2:Nat)^b≤2^1 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  refine ⟨hb,?_⟩
  rw [pcast]
  have hi := Int.ofNat_lt.mpr hn
  simpa using hi

private theorem rep_bounds (b x y : Nat) (s : Offset) (hs : small b s=true)
    (hr : Rep b x y s) : 2≤b ∧ 5<x ∧ 8≤y ∧ p b<2*((x:Int)+(y:Int)) := by
  obtain ⟨hb,hsmall⟩ := small_facts b s hs
  obtain ⟨A,B,hA,hB,hleft,hx,hy⟩ := hr
  have ha := Int.mul_nonneg (Int.le_of_lt (ppos b)) hA
  have hb' : p b≤p b*B := by simpa using Int.mul_le_mul_of_nonneg_left hB (Int.le_of_lt (ppos b))
  have hxl := abs_lower s.x
  have hyl := abs_lower s.y
  have hxx : 5<x := by
    rcases hleft with h1 | h1
    · have hh : p b≤p b*A := by simpa using Int.mul_le_mul_of_nonneg_left h1 (Int.le_of_lt (ppos b))
      omega
    · omega
  exact ⟨hb,hxx,by omega,by omega⟩

private theorem emod_rep (b r : Nat) (A s : Int) (h : r≤b) :
    (p b*A+s)%p r=s%p r := by
  have hd : p r∣p b*A := Int.dvd_trans (pdvd b r h) (Int.dvd_mul_right _ _)
  rw [Int.add_emod, Int.emod_eq_zero_of_dvd hd]
  simp

private theorem parity_match (b x y : Nat) (s : Offset) (hb : 2≤b) (hr : Rep b x y s) :
    (x:Int)%2=s.x%2 ∧ (y:Int)%2=s.y%2 ∧ ((x+y)%2:Nat)=(oddPart s).toNat := by
  obtain ⟨A,B,_,_,_,hx,hy⟩ := hr
  have h1 := emod_rep b 1 A s.x (by omega)
  have h2 := emod_rep b 1 B s.y (by omega)
  change (p b*A+s.x)%2=s.x%2 at h1
  change (p b*B+s.y)%2=s.y%2 at h2
  rw [←hx] at h1
  rw [←hy] at h2
  unfold oddPart
  exact ⟨h1,h2,by omega⟩

private theorem bad_sound (reach : Nat → Nat → Prop)
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (b x y : Nat) (s : Offset) (hs : small b s=true) (hr : Rep b x y s)
    (hd : bad s=true) : ¬reach x y := by
  obtain ⟨hb,_,hy,_⟩ := rep_bounds b x y s hs hr
  obtain ⟨hodd,hbad⟩ := of_decide_eq_true hd
  obtain ⟨_,hy2,_⟩ := parity_match b x y s hb hr
  obtain ⟨A,B,_,_,_,hx,hy'⟩ := hr
  have h1 := emod_rep b 2 A s.x hb
  have h2 := emod_rep b 2 B s.y hb
  change (p b*A+s.x)%4=s.x%4 at h1
  change (p b*B+s.y)%4=s.y%4 at h2
  rw [←hx] at h1
  rw [←hy'] at h2
  exact forbid x y (by omega) (by omega) (by omega)

private theorem actual_valuation (b x y : Nat) (s : Offset) (hs : small b s=true)
    (hr : Rep b x y s) (hv : validVal b s=true) :
    (x+y+(x+y)%2)%2^(val s+1)=2^val s ∧ 2^val s<x+y+(x+y)%2 := by
  obtain ⟨hb,_,_,hsize⟩ := rep_bounds b x y s hs hr
  obtain ⟨hvb,hvmod⟩ := of_decide_eq_true hv
  obtain ⟨_,_,ho⟩ := parity_match b x y s hb hr
  have ho' : ((x+y)%2:Nat) = (oddPart s).toNat := ho
  have hnonneg : 0≤oddPart s := Int.emod_nonneg _ (by decide)
  obtain ⟨A,B,_,_,_,hx,hy⟩ := hr
  have hq : (↑(x+y+(x+y)%2):Int)=p b*(A+B)+rounded s := by
    unfold rounded
    rw [Int.mul_add]
    omega
  have hh := emod_rep b (val s+1) (A+B) (rounded s) hvb
  rw [←hq,hvmod,pcast,pcast,←Int.natCast_emod] at hh
  have hp : (2:Nat)^(val s+1)≤2^b := Nat.pow_le_pow_right (by decide) hvb
  rw [Nat.pow_succ] at hp
  rw [pcast] at hsize
  exact ⟨Int.ofNat_inj.mp hh,by omega⟩

private theorem dir_rep (b x y a k : Nat) (s : Offset) (hb : 1≤b)
    (hr : Rep b x y s) (ha : a+2=x+y) (hk : 2*k+2=y)
    (hd : dirValid s (dir s)=true) : Rep (b-1) a k (dir s) := by
  obtain ⟨A,B,hA,hB,_,hx,hy⟩ := hr
  obtain ⟨hdx,hdy⟩ := of_decide_eq_true hd
  have hp : p b=2*p (b-1) := by conv => lhs; rw [show b=b-1+1 by omega,psucc]
  have hcoef : 1≤2*(A+B) := by omega
  refine ⟨2*(A+B),B,by omega,hB,Or.inl hcoef,?_,?_⟩
  · have he : p (b-1)*(2*(A+B))=p b*A+p b*B := by rw [hp,←Int.mul_add]; ac_rfl
    rw [he]
    omega
  · have he : p b*B=2*(p (b-1)*B) := by rw [hp,Int.mul_assoc]
    omega

private theorem hi_rep (b x y a k n : Nat) (s : Offset) (hb : n+2≤b)
    (hr : Rep b x y s) (ho : ((x+y)%2:Nat)=(oddPart s).toNat)
    (ha : x+y+(x+y)%2=2^(n+1)*(a+2+(x+y)%2))
    (hk : 2*k+a+7+3*n=x+2*y)
    (hv : hiValid s (hi s n) n=true) : Rep (b-(n+2)) a k (hi s n) := by
  obtain ⟨A,B,hA,hB,_,hx,hy⟩ := hr
  obtain ⟨hax,hky⟩ := of_decide_eq_true hv
  let R := p (b-(n+2))
  let D := p (n+1)
  have hD : 0<D := ppos _
  have hD2 : 2≤D := by dsimp [D]; rw [psucc]; have hh:=ppos n; omega
  have hP : p b=2*R*D := by
    rw [psplit b (n+2) hb,show n+2=n+1+1 by omega,psucc]
    dsimp [R,D]
    ac_rfl
  have hnonneg : 0≤oddPart s := Int.emod_nonneg _ (by decide)
  have hq : (↑(x+y+(x+y)%2):Int)=p b*(A+B)+rounded s := by
    unfold rounded
    rw [Int.mul_add]
    omega
  have ha' := congrArg Int.ofNat ha
  change (x:Int)+(y:Int)+((x+y)%2:Nat)=D*((a:Int)+2+((x+y)%2:Nat)) at ha'
  have haQ : D*((a:Int)+2+oddPart s)=p b*(A+B)+rounded s := by
    rw [←hq]
    have hO : (↑((x+y)%2):Int)=oddPart s := by omega
    rw [←hO]
    simpa only [Int.natCast_add] using ha'.symm
  have haR : (a:Int)=R*(2*(A+B))+(hi s n).x := by
    apply Int.eq_of_mul_eq_mul_left (Int.ne_of_gt hD)
    have hprod : D*(R*(2*(A+B)))=p b*(A+B) := by rw [hP]; ac_rfl
    change D*((hi s n).x+2+oddPart s)=rounded s at hax
    simp only [Int.mul_add] at haQ hax ⊢
    simp only [Int.mul_add] at hprod
    omega
  let C := D*(A+2*B)-(A+B)
  have hC : 1≤C := by
    have hh := Int.mul_le_mul_of_nonneg_right hD2 (show 0≤A+2*B by omega)
    dsimp [C]
    omega
  refine ⟨2*(A+B),C,by omega,hC,Or.inl (by omega),haR,?_⟩
  have he1 : p b*(A+2*B)=2*(R*(D*(A+2*B))) := by rw [hP]; ac_rfl
  have he2 : R*(2*(A+B))=2*(R*(A+B)) := by ac_rfl
  have he3 : R*C=R*(D*(A+2*B))-R*(A+B) := by dsimp [C]; rw [Int.mul_sub]
  have hw : (x:Int)+2*(y:Int)=p b*(A+2*B)+mass s := by
    unfold mass
    rw [Int.mul_add,show p b*(2*B)=2*(p b*B) by ac_rfl]
    omega
  change (k:Int)=R*C+(hi s n).y
  rw [he3]
  omega

/-- Fully checked generic signed-residue cone theorem, independent of the
    exact exponential leading coefficients. -/
theorem check_sound (reach : Nat → Nat → Prop)
    (parent : ParentContract reach)
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (f b x y : Nat) (s : Offset) (hc : check f b s=true) (hr : Rep b x y s) : ¬reach x y := by
  induction f generalizing b x y s with
  | zero =>
    simp only [check,Bool.and_eq_true] at hc
    exact bad_sound reach forbid b x y s hc.1 hr hc.2
  | succ f ih =>
    simp only [check,Bool.and_eq_true,Bool.or_eq_true] at hc
    obtain ⟨hs,hrest⟩ := hc
    rcases hrest with hl | ⟨⟨hv,hd⟩,hh⟩
    · exact bad_sound reach forbid b x y s hs hr hl
    · intro hreach
      obtain ⟨hb,hx,hy,_⟩ := rep_bounds b x y s hs hr
      obtain ⟨hval,hgt⟩ := actual_valuation b x y s hs hr hv
      obtain ⟨hvb,_⟩ := of_decide_eq_true hv
      obtain ⟨px,py,ho⟩ := parity_match b x y s hb hr
      obtain ⟨a,k,hreach',hp⟩ := parent x y (val s) hx hy hval hgt hreach
      rcases hp with ⟨hye,ha,hk⟩ | ⟨n,hn,hpar,ha,hk⟩
      · have hsy : s.y%2=0 := by omega
        simp only [hsy,ite_true,Bool.and_eq_true] at hd
        exact ih (b-1) a k (dir s) hd.2 (dir_rep b x y a k s (by omega) hr ha hk hd.1) hreach'
      · have hp' : depthOK s n=true := by
          apply decide_eq_true
          have hnonneg : 0≤oddPart s := Int.emod_nonneg _ (by decide)
          exact ⟨hn,by omega⟩
        have hmem : n∈List.range (val s+1) := List.mem_range.mpr (by omega)
        have hchk := (List.all_eq_true.mp hh) n hmem
        simp only [hp',ite_true,Bool.and_eq_true] at hchk
        exact ih (b-(n+2)) a k (hi s n) hchk.2
          (hi_rep b x y a k n s (by omega) hr ho ha hk hchk.1) hreach'

#print axioms check_sound
end BB6.Agent12SignedCone
