import AnchorDecision
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321Basin
open BB6.Agent31F321Density
open BB6.Agent2F321Bulk
open BB6.Agent2F321Diagonal
open BB6.Agent2F321WordGuard
open BB6.Agent2F321RootWord
open BB6.Agent2F321PrefixSparsity
open BB6.Agent2F321DangerCount

/-- The two reset types have distinct affine formulas. The parity guard
    is retained in both Middle outputs. -/
inductive Reset : Bool → Nat → Nat → Nat → Nat → Prop where
  | equal (a : Nat) : Reset true a a (2*a+4) 1
  | middleEven (a d : Nat) (h1 : a<d) (h2 : d<3*a+1) (hp : (d-a)%2=0) :
      Reset false a d (4*a+6) 2
  | middleOdd (a d : Nat) (h1 : a<d) (h2 : d<3*a+1) (hp : (d-a)%2=1) :
      Reset false a d (4*a+6) 1

def Epoch (R c U e : Nat) : Prop := ∃ w a d b, WordRun w R c a d ∧ Reset b a d U e

def Basin : Nat → Nat → Nat → Prop
  | 0, R, c => DangerousAnchor R c
  | j+1, R, c => DangerousAnchor R c ∨
      (c=1∨c=2) ∧ ∃ U e, Epoch R c U e ∧ Basin j U e

theorem reset_output_small {b a d U e} (hr : Reset b a d U e) : e=1∨e=2 := by
  cases hr <;> simp

theorem reset_output_bound {b a d U e} (hr : Reset b a d U e) : U≤2*(a+d)+4 := by
  cases hr <;> omega

theorem basin_small {j R c} (hb : Basin j R c) : c=1∨c=2 := by
  cases j with
  | zero => exact hb.1
  | succ j => exact hb.elim (fun h=>h.1) (fun h=>h.1)

private theorem pow_two_lower (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

private theorem high_start_data {h c R a d} (hh : HighRun h R c a d) :
    a+d=R+c+h ∧ d+3=2^h*(c+3) := by
  have he := high_run_coordinates hh
  unfold X Y at he
  have hm : 2^h*(2*(c+3))=2*(2^h*(c+3)) := by ac_rfl
  rw [hm] at he
  omega

private theorem firstFar_rank {h c R a d A D w}
    (hc : c=1∨c=2) (hh : HighRun h R c a d)
    (hw : WordRun (.far::w) a d A D) : a+d+5≤7*2^h := by
  have he := (high_start_data hh).2
  have hd : d+3≤5*2^h := by rw [he]; rcases hc with rfl|rfl <;> omega
  cases hw with
  | far h1 h2 ht => omega

/-- A common Far-headed prefix of cost m or m+1 bounds its anchor
    diameter by 16*2^(k-m), uniformly over h≤k and both c values. -/
theorem long_prefix_diameter {k m h c R R' a d b e A D B E : Nat} {w : List InverseLetter}
    (hm : 2≤m) (hmk : m≤k) (hhk : h≤k) (hc : c=1∨c=2)
    (hlo : m≤S (.far::w)) (hhi : S (.far::w)≤m+1)
    (hH : HighRun h R c a d) (hH' : HighRun h R' c b e)
    (hw : WordRun (.far::w) a d A D) (hw' : WordRun (.far::w) b e B E)
    (hle : R≤R') : R'<R+16*2^(k-m) := by
  have h1 := high_start_data hH
  have h2 := high_start_data hH'
  have hde : d=e := by omega
  subst e
  have hsum := firstFar_rank hc hH hw
  have hcost := word_cost_le (.far::w)
  have hrank := word_rank hw
  have hpow : 2^h≤2^k := Nat.pow_le_pow_right (by decide) hhk
  have hk := pow_two_lower k
  have hD : D≤10*2^k := by omega
  have hcost' : m-2≤S w := by simp at hlo; omega
  have hp : 2^(m-2)≤P w := by rw [P_eq_pow]; exact Nat.pow_le_pow_right (by decide) hcost'
  by_cases hdif : R'<R+16*2^(k-m)
  · exact hdif
  · have hdelta : 16*2^(k-m)≤b-a := by omega
    have hgap := firstFar_gap (δ:=b-a) hw hw' (by omega)
    have hmul := Nat.mul_le_mul hp hdelta
    have hmul' : P w*(3*(b-a))=3*(P w*(b-a)) := by ac_rfl
    rw [hmul'] at hgap
    have heq : 2^(m-2)*(16*2^(k-m))=4*2^k := by
      have hexp : (m-2)+(k-m)=k-2 := by omega
      rw [show 2^(m-2)*(16*2^(k-m))=16*(2^(m-2)*2^(k-m)) by ac_rfl,←Nat.pow_add,hexp]
      have hk2 : k-2+2=k := by omega
      have hpow := Nat.pow_add 2 (k-2) 2
      rw [hk2] at hpow
      change 2^k=2^(k-2)*4 at hpow
      omega
    rw [heq] at hmul
    omega

theorem reset_formula {b a d U e} (hr : Reset b a d U e) :
    U=if b then a+d+4 else 4*a+6 := by cases hr <;> simp <;> omega

/-- A short epoch's final reset is injective within a fixed h,c,word,
    reset type and target. It follows from the exact opposite-order gap. -/
theorem short_reset_unique {h c R R' a d a' d' A D B E U e : Nat} {w : List InverseLetter} {b : Bool}
    (hh : HighRun h R c a d) (hh' : HighRun h R' c a' d')
    (hw : WordRun w a d A D) (hw' : WordRun w a' d' B E)
    (hr : Reset b A D U e) (hr' : Reset b B E U e) : R=R' := by
  have h1 := high_start_data hh
  have h2 := high_start_data hh'
  have hdd : d=d' := by omega
  subst d'
  have hR1 := reset_formula hr
  have hR3 := reset_formula hr'
  have hEq (δ : Nat) (hx : A+D+δ=B+E) (hv : E≤D) : δ=0 := by
    cases b <;> simp_all <;> omega
  have hEq' (δ : Nat) (hx : B+E+δ=A+D) (hv : D≤E) : δ=0 := by
    cases b <;> simp_all <;> omega
  by_cases he : R≤R'
  · have hgap := word_gap (δ:=R'-R) (ε:=0) hw hw' (by omega) (by omega)
    have hv : E≤D := by simpa using hgap.2
    have hz := hEq _ hgap.1 hv
    omega
  · have hgap := word_gap (δ:=R-R') (ε:=0) hw' hw (by omega) (by omega)
    have hv : D≤E := by simpa using hgap.2
    have hz := hEq' _ hgap.1 hv
    omega

theorem short_reset_target_bound {k m h c R a d A D U e : Nat} {w : List InverseLetter} {b : Bool}
    (hmk : m≤k) (hhk : h≤k) (hc : c=1∨c=2) (hR : R≤2^k)
    (hS : S w<m) (hh : HighRun h R c a d) (hw : WordRun w a d A D)
    (hr : Reset b A D U e) : U≤2^(k+4) := by
  have hs := (high_start_data hh).1
  have hcost := word_cost_le w
  have hrank := word_rank hw
  have hu := reset_output_bound hr
  have hk := pow_two_lower k
  have hc' : c≤2 := by omega
  rw [Nat.pow_add]
  change U≤2^k*16
  omega

/-- A long code consists of a feasible Far-headed prefix crossing m. -/
def LongCode (k m h c : Nat) (u : List InverseLetter) (R : Nat) : Prop :=
  R≤2^k ∧ m≤S u ∧ S u≤m+1 ∧
  ∃ v a d A D, u=.far::v ∧ HighRun h R c a d ∧ WordRun u a d A D

/-- A short reset code fixes the entire tail and the reset type. -/
def ShortCode (k m h c : Nat) (u : List InverseLetter) (target : Nat×Nat) (b : Bool) (R : Nat) : Prop :=
  R≤2^k ∧ S u<m ∧ ∃ a d A D,
    HighRun h R c a d ∧ WordRun u a d A D ∧ Reset b A D target.1 target.2

noncomputable def longCenter (k m h c : Nat) (u : List InverseLetter) : Nat := by
  classical
  exact if he : ∃ R, LongCode k m h c u R then Classical.choose he else 0

noncomputable def shortDecode (k m h c : Nat) (u : List InverseLetter) (target : Nat×Nat) (b : Bool) : Nat := by
  classical
  exact if he : ∃ R, ShortCode k m h c u target b R then Classical.choose he else 0

theorem longCenter_spec {k m h c u R} (hr : LongCode k m h c u R) :
    LongCode k m h c u (longCenter k m h c u) := by
  classical
  unfold longCenter
  split
  · exact Classical.choose_spec ‹∃ R, LongCode k m h c u R›
  · rename_i hn; exact False.elim (hn ⟨R,hr⟩)

theorem shortDecode_of_code {k m h c u target b R} (hr : ShortCode k m h c u target b R) :
    shortDecode k m h c u target b=R := by
  classical
  unfold shortDecode
  split
  · have hh := Classical.choose_spec ‹∃ R, ShortCode k m h c u target b R›
    rcases hh with ⟨_,_,a,d,A,D,hH,hw,hrst⟩
    rcases hr with ⟨_,_,a',d',B,E,hH',hw',hrst'⟩
    exact short_reset_unique hH hH' hw hw' hrst hrst'
  · rename_i hn; exact False.elim (hn ⟨R,hr⟩)

def diameter (k m : Nat) : Nat := 16*2^(k-m)

noncomputable def longCodeCover (k m h c : Nat) (u : List InverseLetter) : List (Nat×Nat) :=
  let center := longCenter k m h c u
  let B := diameter k m
  (List.range (2*B+1)).map (fun n => (center-B+n,c))

theorem long_code_mem {k m h c u R} (hm : 2≤m) (hmk : m≤k) (hhk : h≤k)
    (hc : c=1∨c=2) (hr : LongCode k m h c u R) : (R,c)∈longCodeCover k m h c u := by
  let center := longCenter k m h c u
  have hc0 : LongCode k m h c u center := longCenter_spec hr
  rcases hr with ⟨_,hlo,hhi,v,a,d,A,D,hu,hh,hw⟩
  rcases hc0 with ⟨_,_,_,v',a',d',B,E,hu',hh',hw'⟩
  subst u
  have he : v'=v := by simpa using hu'.symm
  subst v'
  have hbounds : R≤center+diameter k m ∧ center≤R+diameter k m := by
    by_cases hle : R≤center
    · have hb := long_prefix_diameter hm hmk hhk hc hlo hhi hh hh' hw hw' hle
      unfold diameter
      omega
    · have hb := long_prefix_diameter hm hmk hhk hc hlo hhi hh' hh hw' hw (by omega)
      unfold diameter
      omega
  unfold longCodeCover
  dsimp only
  apply List.mem_map.mpr
  refine ⟨R-(center-diameter k m),List.mem_range.mpr ?_,?_⟩
  · omega
  · change (center-diameter k m+(R-(center-diameter k m)),c)=(R,c)
    congr 1
    omega

/-- Uniform length bound for nested finite covers. -/
private theorem flat_length_le {α β : Type} (xs : List α) (f : α→List β) (M : Nat)
    (hf : ∀ x∈xs, (f x).length≤M) : (xs.flatMap f).length≤xs.length*M := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := hf x (by simp)
      have ht := ih (fun y hy=>hf y (by simp [hy]))
      simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

noncomputable def shortCodeCover (k m h c : Nat) (u : List InverseLetter)
    (targets : List (Nat×Nat)) : List (Nat×Nat) :=
  targets.flatMap (fun p=>[(shortDecode k m h c u p false,c),
                           (shortDecode k m h c u p true,c)])

noncomputable def oneCodeCover (k m h c : Nat) (u : List InverseLetter)
    (targets : List (Nat×Nat)) : List (Nat×Nat) :=
  longCodeCover k m h c u ++ shortCodeCover k m h c u targets

noncomputable def oneHCover (k m h c : Nat) (targets : List (Nat×Nat)) : List (Nat×Nat) :=
  (wordsThrough (m+1)).flatMap (fun u=>oneCodeCover k m h c u targets)

noncomputable def epochPreCover (k m : Nat) (targets : List (Nat×Nat)) : List (Nat×Nat) :=
  (List.range (k+1)).flatMap (fun h=>oneHCover k m h 1 targets ++ oneHCover k m h 2 targets)

theorem oneCodeCover_length {k m h c u targets} :
    (oneCodeCover k m h c u targets).length ≤ 2*diameter k m+1+2*targets.length := by
  have hs : (shortCodeCover k m h c u targets).length≤targets.length*2 :=
    flat_length_le _ _ _ (by intro p hp; simp)
  unfold oneCodeCover longCodeCover
  simp only [List.length_append,List.length_map,List.length_range]
  omega

theorem oneHCover_length {k m h c targets} :
    (oneHCover k m h c targets).length ≤
      fib (m+4)*(2*diameter k m+1+2*targets.length) := by
  have h := flat_length_le (wordsThrough (m+1))
    (fun u=>oneCodeCover k m h c u targets) _ (fun u _=>oneCodeCover_length)
  have hf := wordsThrough_count (m+1)
  have he : m+1+3=m+4 := by omega
  rw [he] at hf
  have hn : (wordsThrough (m+1)).length≤fib (m+4) := by omega
  exact Nat.le_trans h (Nat.mul_le_mul_right _ hn)

theorem epochPreCover_length {k m targets} :
    (epochPreCover k m targets).length ≤
      2*(k+1)*fib (m+4)*(2*diameter k m+1+2*targets.length) := by
  let B := fib (m+4)*(2*diameter k m+1+2*targets.length)
  have h := flat_length_le (List.range (k+1))
    (fun h=>oneHCover k m h 1 targets ++ oneHCover k m h 2 targets) (2*B) (by
      intro h hh
      have h1 := oneHCover_length (k:=k) (m:=m) (h:=h) (c:=1) (targets:=targets)
      have h2 := oneHCover_length (k:=k) (m:=m) (h:=h) (c:=2) (targets:=targets)
      simp only [List.length_append]
      dsimp [B]
      omega)
  simp only [List.length_range] at h
  unfold epochPreCover
  dsimp [B] at h
  exact Nat.le_trans h (by rw [show (k+1)*(2*(fib (m+4)*(2*diameter k m+1+2*targets.length)))=
    2*(k+1)*fib (m+4)*(2*diameter k m+1+2*targets.length) by ac_rfl]; exact Nat.le_refl _)

private theorem oneCode_mem_long {k m h c u R targets} (hm : 2≤m) (hmk : m≤k) (hhk : h≤k)
    (hc : c=1∨c=2) (hr : LongCode k m h c u R) : (R,c)∈oneHCover k m h c targets := by
  apply List.mem_flatMap.mpr
  refine ⟨u,word_mem_through _ _ hr.2.2.1,?_⟩
  exact List.mem_append.mpr (Or.inl (long_code_mem hm hmk hhk hc hr))

private theorem oneCode_mem_short {k m h c u R targets p b} (hp : p∈targets)
    (hr : ShortCode k m h c u p b R) : (R,c)∈oneHCover k m h c targets := by
  apply List.mem_flatMap.mpr
  refine ⟨u,word_mem_through _ _ (by have hh:=hr.2.1; omega),?_⟩
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  refine ⟨p,hp,?_⟩
  have he := shortDecode_of_code hr
  cases b <;> simp [he]

private theorem oneH_mem_epochCover {k m h c R targets} (hhk : h≤k) (hc : c=1∨c=2)
    (hr : (R,c)∈oneHCover k m h c targets) : (R,c)∈epochPreCover k m targets := by
  apply List.mem_flatMap.mpr
  refine ⟨h,List.mem_range.mpr (by omega),?_⟩
  rcases hc with rfl|rfl
  · exact List.mem_append.mpr (Or.inl hr)
  · exact List.mem_append.mpr (Or.inr hr)

/-- A finite cover for the predecessor of an arbitrary target set. Short
    epochs are bounded by targets at the larger scale 2^(k+4); all long
    epochs are covered regardless of their eventual output scale. -/
theorem epochPreCover_complete {k m R c U e targets} (hm : 2≤m) (hmk : m≤k)
    (hc : c=1∨c=2) (hR : R≤2^k) (he : Epoch R c U e)
    (hTarget : U≤2^(k+4) → (U,e)∈targets) : (R,c)∈epochPreCover k m targets := by
  rcases he with ⟨w,a,d,b,hw,hr⟩
  rcases word_split_high hw with ⟨h,u,A,D,_,hh,hu,hs⟩
  have hhk := leadingHigh_le (by omega : 2≤k) hR hc hh
  apply oneH_mem_epochCover hhk hc
  by_cases hshort : S u<m
  · have hU := short_reset_target_bound hmk hhk hc hR hshort hh hu hr
    exact oneCode_mem_short (p:=(U,e)) (b:=b) (hTarget hU) ⟨hR,hshort,A,D,a,d,hh,hu,hr⟩
  · rcases hs with rfl | ⟨v,rfl⟩
    · simp at hshort
      omega
    · rcases prefix_cross hu (m:=m) (by omega) (by omega) with ⟨p,q,B,E,hword,hp,hlo,hhi⟩
      cases p with
      | nil => simp at hlo; omega
      | cons z p =>
          have hz : z=.far := by simpa using congrArg List.head? hword.symm
          subst z
          exact oneCode_mem_long hm hmk hhk hc ⟨hR,hlo,hhi,p,A,D,B,E,rfl,hh,hp⟩

#print axioms long_prefix_diameter
#print axioms short_reset_unique
#print axioms long_code_mem
#print axioms epochPreCover_length
#print axioms epochPreCover_complete
end BB6.Agent2F321Basin
