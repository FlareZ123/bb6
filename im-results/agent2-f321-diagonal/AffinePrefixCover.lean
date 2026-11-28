import WordDangerCount
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321AffinePrefix
open BB6.Agent31F321Density
open BB6.Agent2F321Bulk
open BB6.Agent2F321Diagonal
open BB6.Agent2F321LastFarExact
open BB6.Agent2F321WordGuard
open BB6.Agent2F321RootWord
open BB6.Agent2F321PrefixSparsity
open BB6.Agent2F321DangerCount

/-- x=R+C, v=B-A R, expressed without division. -/
structure Affine where
  A : Nat
  B : Int
  C : Int
  deriving Repr

def initial (h c : Nat) : Affine := ⟨0, (2^h*(c+3):Nat), (c+5+h:Nat)⟩
def Affine.x (f : Affine) (R : Nat) : Int := (R:Int)+f.C
def Affine.v (f : Affine) (R : Nat) : Int := f.B-(f.A:Int)*(R:Int)
def Affine.high (f : Affine) : Affine := ⟨2*f.A,2*f.B,f.C+1⟩
def Affine.far (f : Affine) : Affine := ⟨4*f.A+3,4*f.B-3*f.C+6,f.C+6⟩
def Affine.step (f : Affine) : InverseLetter → Affine
  | .high => f.high
  | .far => f.far

def Matches (f : Affine) (R a d : Nat) : Prop :=
  f.x R=(a:Int)+d+5 ∧ f.v R=(d:Int)+3

theorem initial_matches {h c R a d} (hh : HighRun h R c a d) : Matches (initial h c) R a d := by
  have he := high_run_coordinates hh
  unfold X Y at he
  have hm : 2^h*(2*(c+3))=2*(2^h*(c+3)) := by ac_rfl
  rw [hm] at he
  unfold Matches initial Affine.x Affine.v
  simp only [Int.natCast_zero,Int.zero_mul,Int.sub_zero]
  omega

theorem high_matches {f R a d} (hf : Matches f R a d) (hg : d+2≤a) :
    Matches f.high R (a-d-2) (2*d+3) := by
  rcases hf with ⟨hx,hv⟩
  unfold Affine.x at hx
  unfold Affine.v at hv
  unfold Matches Affine.x Affine.v Affine.high
  simp only [Int.natCast_mul,Int.mul_assoc]
  omega

theorem far_matches {f R a d} (hf : Matches f R a d) (hg : 3*a+1≤d) :
    Matches f.far R (4*a+6) (d-3*a) := by
  rcases hf with ⟨hx,hv⟩
  unfold Affine.x at hx
  unfold Affine.v at hv
  unfold Matches Affine.x Affine.v Affine.far
  simp only [Int.natCast_add,Int.natCast_mul,Int.add_mul,Int.mul_assoc]
  omega

/-- Integer interval in the original anchor R. Empty iff hi<lo. -/
structure Interval where
  lo : Int
  hi : Int
  deriving Repr

def In (i : Interval) (R : Nat) : Prop := i.lo≤(R:Int) ∧ (R:Int)≤i.hi

def highInterval (f : Affine) (i : Interval) : Interval :=
  ⟨max i.lo (-((f.C-2*f.B-1)/(2*(f.A:Int)+1))),i.hi⟩
def farInterval (f : Affine) (i : Interval) : Interval :=
  ⟨i.lo,min i.hi ((4*f.B-3*f.C+2)/(4*(f.A:Int)+3))⟩

private theorem floor_iff (b p r : Int) (hp : 0<p) : r≤b/p ↔ p*r≤b := by
  rw [Int.le_ediv_iff_mul_le hp,Int.mul_comm r p]

private theorem ceil_iff (b p r : Int) (hp : 0<p) : -( (-b)/p)≤r ↔ b≤p*r := by
  have he := floor_iff (-b) p (-r) hp
  rw [Int.mul_neg] at he
  omega

theorem high_interval_iff {f i R a d} (hf : Matches f R a d) :
    In (highInterval f i) R ↔ In i R ∧ d+2≤a := by
  rcases hf with ⟨hx,hv⟩
  unfold Affine.x at hx
  unfold Affine.v at hv
  unfold In highInterval
  simp only [Int.max_le]
  have hp : 0<2*(f.A:Int)+1 := by omega
  have he := ceil_iff (2*f.B-f.C+1) (2*(f.A:Int)+1) (R:Int) hp
  have hneg : -(2*f.B-f.C+1)=f.C-2*f.B-1 := by omega
  rw [hneg] at he
  rw [he]
  simp only [Int.add_mul,Int.one_mul,Int.mul_assoc]
  omega

theorem far_interval_iff {f i R a d} (hf : Matches f R a d) :
    In (farInterval f i) R ↔ In i R ∧ 3*a+1≤d := by
  rcases hf with ⟨hx,hv⟩
  unfold Affine.x at hx
  unfold Affine.v at hv
  unfold In farInterval
  simp only [Int.le_min]
  have hp : 0<4*(f.A:Int)+3 := by omega
  rw [floor_iff _ _ _ hp]
  simp only [Int.add_mul,Int.mul_assoc]
  omega

/-- Constructive forward interval compiler. It never enumerates R. -/
def compileInterval : List InverseLetter → Affine → Interval → Affine × Interval
  | [], f, i => (f,i)
  | .high::w, f, i => compileInterval w f.high (highInterval f i)
  | .far::w, f, i => compileInterval w f.far (farInterval f i)

theorem compile_subset {w f i R} (hi : In (compileInterval w f i).2 R) : In i R := by
  induction w generalizing f i with
  | nil => exact hi
  | cons z w ih =>
      cases z with
      | high =>
          have ht := ih (f:=f.high) (i:=highInterval f i) hi
          unfold In highInterval at ht
          simp only [Int.max_le] at ht
          exact ⟨ht.1.1,ht.2⟩
      | far =>
          have ht := ih (f:=f.far) (i:=farInterval f i) hi
          unfold In farInterval at ht
          simp only [Int.le_min] at ht
          exact ⟨ht.1,ht.2.1⟩

/-- Exact, source-faithful interval feasibility and affine endpoint. -/
theorem compile_interval_iff {w f i R a d} (hf : Matches f R a d) :
    In (compileInterval w f i).2 R ↔
      In i R ∧ ∃ A D, WordRun w a d A D ∧ Matches (compileInterval w f i).1 R A D := by
  induction w generalizing f i a d with
  | nil =>
      simp only [compileInterval]
      constructor
      · intro hi; exact ⟨hi,a,d,WordRun.nil a d,hf⟩
      · rintro ⟨hi,_,_,_,_⟩; exact hi
  | cons z w ih =>
      cases z with
      | high =>
          simp only [compileInterval]
          constructor
          · intro hi
            have hg0 : In (highInterval f i) R := compile_subset hi
            rcases (high_interval_iff hf).mp hg0 with ⟨hI,hg⟩
            rcases (ih (high_matches hf hg)).mp hi with ⟨_,A,D,hw,hm⟩
            exact ⟨hI,A,D,WordRun.high hg hw,hm⟩
          · rintro ⟨hi,A,D,hw,hm⟩
            cases hw with
            | high hg ht =>
              exact (ih (high_matches hf hg)).mpr ⟨(high_interval_iff hf).mpr ⟨hi,hg⟩,A,D,ht,hm⟩
      | far =>
          simp only [compileInterval]
          constructor
          · intro hi
            have hg0 : In (farInterval f i) R := compile_subset hi
            rcases (far_interval_iff hf).mp hg0 with ⟨hI,hg⟩
            rcases (ih (far_matches hf hg)).mp hi with ⟨_,A,D,hw,hm⟩
            exact ⟨hI,A,D,WordRun.far (by omega) hg hw,hm⟩
          · rintro ⟨hi,A,D,hw,hm⟩
            cases hw with
            | far h1 h2 ht =>
              exact (ih (far_matches hf h2)).mpr ⟨(far_interval_iff hf).mpr ⟨hi,h2⟩,A,D,ht,hm⟩

theorem word_matches {w f i R a d A D} (hf : Matches f R a d) (hw : WordRun w a d A D) :
    Matches (compileInterval w f i).1 R A D := by
  induction hw generalizing f i with
  | nil => exact hf
  | high hg _ ih => exact ih (high_matches hf hg)
  | far _ hg _ ih => exact ih (far_matches hf hg)

/-- Restrict the leading High block by the nonnegative endpoint, an exact
    condition established in highRun_of_balances. -/
def initialInterval (h c N : Nat) : Interval :=
  ⟨((2^h*(c+3):Nat):Int)-((c+h+3:Nat):Int), N⟩

-- A nonnegative R is implicit in In. The lower bound may be negative.
theorem initial_interval_iff {h c N R : Nat} : In (initialInterval h c N) R ↔
    R≤N ∧ ∃ a d, HighRun h R c a d := by
  have hv : 3≤2^h*(c+3) := by
    have hp : 1≤2^h := Nat.one_le_pow _ _ (by decide)
    have hm := Nat.mul_le_mul_right (c+3) hp
    simp at hm
    omega
  unfold In initialInterval
  dsimp only
  constructor
  · intro hi
    let d := 2^h*(c+3)-3
    let a := R+c+h-d
    have hD : d+3=2^h*(c+3) := by dsimp [d]; omega
    have hA : a+d=R+c+h := by dsimp [a]; omega
    exact ⟨by omega,a,d,highRun_of_balances hA hD⟩
  · rintro ⟨hN,a,d,hh⟩
    have hm := initial_matches hh
    unfold Matches initial Affine.x Affine.v at hm
    simp only [Int.natCast_zero,Int.zero_mul,Int.sub_zero] at hm
    omega

def anchorCompile (h c N : Nat) (w : List InverseLetter) : Affine × Interval :=
  compileInterval w (initial h c) (initialInterval h c N)

theorem anchor_compile_iff {h c N R : Nat} {w : List InverseLetter} :
    In (anchorCompile h c N w).2 R ↔ R≤N ∧ ∃ a d A D,
      HighRun h R c a d ∧ WordRun w a d A D ∧ Matches (anchorCompile h c N w).1 R A D := by
  constructor
  · intro hi
    have hi0 := compile_subset hi
    rcases initial_interval_iff.mp hi0 with ⟨hN,a,d,hh⟩
    rcases (compile_interval_iff (initial_matches hh)).mp hi with ⟨_,A,D,hw,hm⟩
    exact ⟨hN,a,d,A,D,hh,hw,hm⟩
  · rintro ⟨hN,a,d,A,D,hh,hw,hm⟩
    exact (compile_interval_iff (initial_matches hh)).mpr
      ⟨initial_interval_iff.mpr ⟨hN,a,d,hh⟩,A,D,hw,hm⟩

/-- Long feasible code intervals contain at most one nonnegative integer. -/
theorem long_interval_unique {h c N R R' : Nat} {w : List InverseLetter}
    (hc : c=1 ∨ c=2) (hs : h+6≤S (.far::w))
    (h1 : In (anchorCompile h c N (.far::w)).2 R)
    (h2 : In (anchorCompile h c N (.far::w)).2 R') : R=R' := by
  rcases anchor_compile_iff.mp h1 with ⟨_,a,d,A,D,hh,hw,_⟩
  rcases anchor_compile_iff.mp h2 with ⟨_,a',d',A',D',hh',hw',_⟩
  exact long_prefix_unique hc hs hh hh' hw hw'

/-- For a terminal short code the exact affine terminal equation determines R.
    For a long code the interval lower endpoint determines R. Empty or invalid
    codes may return an irrelevant integer; the cover theorem needs only
    completeness and a uniform finite size. -/
def decodeAt (h c N : Nat) (w : List InverseLetter) : Nat :=
  let (f,i) := anchorCompile h c N w
  if S w<h+6 then ((2*f.B-f.C)/(2*(f.A:Int)+1)).toNat
  else i.lo.toNat

theorem decodeAt_of_code {h c N R : Nat} {w : List InverseLetter}
    (hc : c=1 ∨ c=2) (hN : R≤N) (hr : CodeRel h c R w) : decodeAt h c N w=R := by
  rcases hr with ⟨hs,t,a,d,hh,hw⟩ | ⟨hl,hu,v,a,d,A,D,he,hh,hw⟩
  · have hm : Matches (anchorCompile h c N w).1 R (t+1) t := word_matches (initial_matches hh) hw
    rcases hm with ⟨hx,hv⟩
    unfold Affine.x at hx
    unfold Affine.v at hv
    let f := (anchorCompile h c N w).1
    change (R:Int)+f.C=((t+1:Nat):Int)+t+5 at hx
    change f.B-(f.A:Int)*(R:Int)=(t:Int)+3 at hv
    have he : 2*f.B-f.C=(2*(f.A:Int)+1)*(R:Int) := by
      rw [Int.add_mul,Int.mul_assoc,Int.one_mul]
      omega
    have hp : 2*(f.A:Int)+1≠0 := by omega
    unfold decodeAt
    simp only [hs,if_true]
    change ((2*f.B-f.C)/(2*(f.A:Int)+1)).toNat=R
    rw [he,Int.mul_comm,Int.mul_ediv_cancel _ hp]
    simp
  · subst w
    have hmem : In (anchorCompile h c N (.far::v)).2 R := anchor_compile_iff.mpr
      ⟨hN,a,d,A,D,hh,hw,word_matches (initial_matches hh) hw⟩
    let i := (anchorCompile h c N (.far::v)).2
    change In i R at hmem
    have hlo : In i i.lo.toNat := by
      unfold In at hmem ⊢
      omega
    have he := long_interval_unique hc hl hmem hlo
    unfold decodeAt
    simp only [show ¬S (.far::v)<h+6 by omega,if_false]
    exact he.symm

#print axioms compile_interval_iff
#print axioms anchor_compile_iff
#print axioms decodeAt_of_code
end BB6.Agent2F321AffinePrefix
