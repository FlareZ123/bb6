import Std.Data.HashMap.Lemmas
import AffineConeLowStop
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 4000000
namespace BB6.Agent13NegativeShadow
open BB6.Agent13AffineCone BB6.Agent46

structure Pair where
  x : Nat
  y : Nat
  deriving Repr,DecidableEq

def mass (s : Pair) : Nat := s.x+2*s.y
def parity (s : Pair) : Nat := (s.x+s.y)%2
def q (s : Pair) : Nat := s.x+s.y-parity s
def small (b : Nat) (s : Pair) : Bool := decide (0<s.x ∧ 0<s.y ∧ (2*(s.x+s.y+8)).log2<b)
def bad (s : Pair) : Bool := decide (s.y%2=1 ∧ ((s.x+s.y)%4=2 ∨ (s.x+s.y)%4=3))
def val (s : Pair) : Nat := v2Aux ((q s).log2+1) (q s)
def validVal (b : Nat) (s : Pair) : Bool := decide (val s+1≤b ∧ q s%2^(val s+1)=2^val s)
def dir (s : Pair) : Pair := ⟨s.x+s.y+2,(s.y+2)/2⟩
def hi (s : Pair) (n : Nat) : Pair :=
  let a := q s/2^(n+1)+2+parity s
  ⟨a,(mass s+7+3*n-a)/2⟩
def validHi (s p : Pair) (n : Nat) : Bool := decide (
  2^(n+1)*p.x=q s+2^(n+1)*(2+parity s) ∧ 2*p.y+p.x=mass s+7+3*n)
def depthOK (s : Pair) (n : Nat) : Bool := decide (n+2≤val s ∧ n%2=(s.x+1+parity s)%2)

def check : Nat → Nat → Pair → Bool
  | 0,b,s => small b s && bad s
  | f+1,b,s => small b s && (bad s || (validVal b s &&
    (if s.y%2=0 then check f (b-1) (dir s) else true) &&
    (List.range (val s+1)).all (fun n => if depthOK s n then
      validHi s (hi s n) n && check f (b-(n+2)) (hi s n) else true)))

def congruent (b x y : Nat) (s : Pair) : Prop := 2^b∣x+s.x ∧ 2^b∣y+s.y

private theorem weaken (b c p : Nat) (hcb : c≤b) (h : 2^b∣p) : 2^c∣p :=
  Nat.dvd_trans (Nat.pow_dvd_pow 2 hcb) h

private theorem cancel_pow (b r p : Nat) (hr : r≤b) (h : 2^b∣2^r*p) : 2^(b-r)∣p := by
  apply Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos (by decide : 0<(2:Nat)))
  rw [Nat.mul_comm (2^r) (2^(b-r)),Nat.pow_sub_mul_pow 2 hr]
  exact h

private theorem complement_half (p q d : Nat) (hd : 0<d)
    (hq : q%(2*d)=d) (h : 2*d∣p+q) : p%(2*d)=d := by
  have hz := Nat.mod_eq_zero_of_dvd h
  rw [Nat.add_mod,hq] at hz
  have hp := Nat.mod_lt p (by omega : 0<2*d)
  obtain ⟨k,hk⟩ := Nat.dvd_of_mod_eq_zero hz
  have hk1 : k=1 := by
    by_cases hk0 : k=0
    · subst k; omega
    · by_cases hne : k=1
      · exact hne
      · have hge : 2≤k := by omega
        have hmul := Nat.mul_le_mul_left (2*d) hge
        omega
  subst k
  omega

private theorem small_bounds (b x y : Nat) (s : Pair)
    (hs : small b s=true) (hc : congruent b x y s) :
    2≤b ∧ 5<x ∧ 8≤y ∧ 2*(s.x+s.y+8)<2^b := by
  obtain ⟨hx,hy,hl⟩ := of_decide_eq_true hs
  have hp := (Nat.log2_lt (by omega : 2*(s.x+s.y+8)≠0)).mp hl
  have hb : 2≤b := by
    by_cases h : 2≤b
    · exact h
    · have hh : 2^b≤2^1 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  have hx' := Nat.le_of_dvd (by omega : 0<x+s.x) hc.1
  have hy' := Nat.le_of_dvd (by omega : 0<y+s.y) hc.2
  exact ⟨hb,by omega,by omega,hp⟩

private theorem parity_match (b x y : Nat) (s : Pair) (hb : 2≤b) (h : congruent b x y s) :
    x%2=s.x%2 ∧ y%2=s.y%2 ∧ (x+y)%2=parity s := by
  have hx := Nat.mod_eq_zero_of_dvd (weaken b 1 (x+s.x) (by omega) h.1)
  have hy := Nat.mod_eq_zero_of_dvd (weaken b 1 (y+s.y) (by omega) h.2)
  change (x+s.x)%2=0 at hx
  change (y+s.y)%2=0 at hy
  unfold parity
  omega

private theorem bad_sound (reach : Nat → Nat → Prop)
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (b x y : Nat) (s : Pair) (hs : small b s=true) (h : congruent b x y s) (hd : bad s=true) : ¬reach x y := by
  obtain ⟨hb,_,hy,_⟩ := small_bounds b x y s hs h
  obtain ⟨hy2,hm⟩ := of_decide_eq_true hd
  have hx4 := Nat.mod_eq_zero_of_dvd (weaken b 2 (x+s.x) hb h.1)
  have hy4 := Nat.mod_eq_zero_of_dvd (weaken b 2 (y+s.y) hb h.2)
  change (x+s.x)%4=0 at hx4
  change (y+s.y)%4=0 at hy4
  exact forbid x y (by omega) (by omega) (by omega)

private theorem actual_valuation (b x y : Nat) (s : Pair)
    (hs : small b s=true) (hc : congruent b x y s) (hv : validVal b s=true) :
    (x+y+(x+y)%2)%2^(val s+1)=2^val s ∧ 2^val s<x+y+(x+y)%2 := by
  obtain ⟨hb,hx,hy,hbig⟩ := small_bounds b x y s hs hc
  obtain ⟨hvb,hvq⟩ := of_decide_eq_true hv
  obtain ⟨_,_,ho⟩ := parity_match b x y s hb hc
  have hsum : 2^b∣(x+y+(x+y)%2)+q s := by
    have hh := Nat.dvd_add hc.1 hc.2
    unfold q parity at *
    rw [show (x+y+(x+y)%2)+(s.x+s.y-(s.x+s.y)%2)=(x+s.x)+(y+s.y) by omega]
    exact hh
  have hh := weaken b (val s+1) _ hvb hsum
  have hpow : 2^(val s+1)=2*2^val s := by rw [Nat.pow_succ,Nat.mul_comm]
  have hmod : (x+y+(x+y)%2)%2^(val s+1)=2^val s := by
    rw [hpow] at hh hvq ⊢
    exact complement_half _ _ _ (Nat.pow_pos (by decide)) hvq hh
  have hle : 2^(val s+1)≤2^b := Nat.pow_le_pow_right (by decide) hvb
  have hxge := Nat.le_of_dvd (by omega : 0<x+s.x) hc.1
  have hqle : q s≤s.x+s.y := Nat.sub_le _ _
  have htot := Nat.le_of_dvd (by omega : 0<(x+y+(x+y)%2)+q s) hsum
  constructor
  · exact hmod
  · rw [hpow] at hle
    omega

private theorem direct_lift (b x y a k : Nat) (s : Pair) (hb : 2≤b)
    (hc : congruent b x y s) (hy : y%2=0)
    (ha : a+2=x+y) (hk : 2*k+2=y) : congruent (b-1) a k (dir s) := by
  obtain ⟨_,hsy,_⟩ := parity_match b x y s hb hc
  have he : s.y%2=0 := by omega
  have h1 : a+(dir s).x=x+s.x+(y+s.y) := by unfold dir; dsimp; omega
  have h2 : 2*(k+(dir s).y)=y+s.y := by unfold dir; dsimp; omega
  constructor
  · rw [h1]; exact weaken b (b-1) _ (by omega) (Nat.dvd_add hc.1 hc.2)
  · have hh : 2^b∣2^1*(k+(dir s).y) := by rw [Nat.pow_one,h2]; exact hc.2
    exact cancel_pow b 1 _ (by omega) hh

private theorem high_lift (b x y a k n : Nat) (s : Pair)
    (hb : 2≤b) (hn : n+2≤b) (hc : congruent b x y s)
    (hvalid : validHi s (hi s n) n=true)
    (ha : x+y+(x+y)%2=2^(n+1)*(a+2+(x+y)%2))
    (hk : 2*k+a+7+3*n=x+2*y) : congruent (b-(n+2)) a k (hi s n) := by
  obtain ⟨_,_,ho⟩ := parity_match b x y s hb hc
  obtain ⟨hA,hK⟩ := of_decide_eq_true hvalid
  have he : q s+parity s=s.x+s.y := by unfold q parity; omega
  have hsum : 2^(n+1)*(a+(hi s n).x)=(x+s.x)+(y+s.y) := by
    rw [ho] at ha
    simp only [Nat.mul_add] at ha hA ⊢
    omega
  have h1 : 2^(b-(n+1))∣a+(hi s n).x := by
    apply cancel_pow b (n+1) _ (by omega)
    rw [hsum]
    exact Nat.dvd_add hc.1 hc.2
  have hsum2 : 2*(k+(hi s n).y)+(a+(hi s n).x)=(x+s.x)+2*(y+s.y) := by
    unfold mass at hK
    omega
  have h2 : 2^b∣2*(k+(hi s n).y)+(a+(hi s n).x) := by
    rw [hsum2]
    apply Nat.dvd_add hc.1
    exact Nat.dvd_trans hc.2 (Nat.dvd_mul_left _ _)
  have h3 := weaken b (b-(n+1)) _ (by omega) h2
  have h4 : 2^(b-(n+1))∣2*(k+(hi s n).y) := by
    have hsub := Nat.dvd_sub h3 h1
    rw [Nat.add_sub_cancel] at hsub
    exact hsub
  have h5 := cancel_pow (b-(n+1)) 1 (k+(hi s n).y) (by omega) (by simpa using h4)
  constructor
  · exact weaken (b-(n+1)) (b-(n+2)) _ (by omega) h1
  · rwa [show b-(n+1)-1=b-(n+2) by omega] at h5

/-- A small negative-counter tree refutes every congruent positive source target,
    while charging exactly one bit per direct edge and n+2 per high edge. -/
theorem check_sound (reach : Nat → Nat → Prop)
    (parent : ∀ x y, 5<x → 8≤y → reach x y → ∃ a k, reach a k ∧ sectionPreimageCriterion a k x y)
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (f b x y : Nat) (s : Pair) (h : check f b s=true) (hc : congruent b x y s) : ¬reach x y := by
  induction f generalizing b x y s with
  | zero =>
    simp only [check,Bool.and_eq_true] at h
    exact bad_sound reach forbid b x y s h.1 hc h.2
  | succ f ih =>
    simp only [check,Bool.and_eq_true,Bool.or_eq_true] at h
    obtain ⟨hs,hrest⟩ := h
    rcases hrest with hl | ⟨⟨hv,hd⟩,hh⟩
    · exact bad_sound reach forbid b x y s hs hc hl
    · intro hr
      obtain ⟨hb,hx,hy,_⟩ := small_bounds b x y s hs hc
      obtain ⟨hval,hgt⟩ := actual_valuation b x y s hs hc hv
      obtain ⟨hvb,_⟩ := of_decide_eq_true hv
      obtain ⟨a,k,hp,he⟩ := parent x y hx hy hr
      obtain ⟨hpx,hpy,hpo⟩ := parity_match b x y s hb hc
      rcases parent_equations a k x y (val s) hy hval hgt he with hdir | hhigh
      · obtain ⟨hye,ha,hk⟩ := hdir
        have hy0 : s.y%2=0 := by omega
        simp only [hy0,ite_true] at hd
        exact ih (b-1) a k (dir s) hd (direct_lift b x y a k s hb hc hye ha hk) hp
      · obtain ⟨n,hn,hpar,ha,hk⟩ := hhigh
        have hn' : n∈List.range (val s+1) := List.mem_range.mpr (by omega)
        have hchk := (List.all_eq_true.mp hh) n hn'
        have hdepth : depthOK s n=true := decide_eq_true ⟨hn,by omega⟩
        simp only [hdepth,ite_true,Bool.and_eq_true] at hchk
        exact ih (b-(n+2)) a k (hi s n) hchk.2
          (high_lift b x y a k n s hb (by omega) hc hchk.1 ha hk) hp

def lowShadow (z : Nat) : Pair := ⟨1080*z+152,996*z+141⟩
def lowShadowExcluded (f z : Nat) : Bool := check f (1024*z+129) (lowShadow z)

theorem lowShadow_congruent (z u : Nat) (hu : u+6*z+1=2^(1024*z+129)) :
    congruent (1024*z+129) (180*u+28) (166*u+25) (lowShadow z) := by
  constructor
  · refine ⟨180,?_⟩
    unfold lowShadow; dsimp
    omega
  · refine ⟨166,?_⟩
    unfold lowShadow; dsimp
    omega

abbrev Cert := Std.HashMap (Nat × Nat) Nat
def key (s : Pair) := (s.x,s.y)
def childOK (c : Cert) (req shift : Nat) (s : Pair) : Bool :=
  match c[key s]? with
  | some r => decide (r+shift≤req)
  | none => false

def nodeOK (c : Cert) (s : Pair) (req : Nat) : Bool :=
  small req s && (bad s || (validVal req s &&
    (if s.y%2=0 then childOK c req 1 (dir s) else true) &&
    (List.range (val s+1)).all (fun n => if depthOK s n then
      validHi s (hi s n) n && childOK c req (n+2) (hi s n) else true)))

def certOK (c : Cert) : Bool := c.all (fun p req => nodeOK c ⟨p.1,p.2⟩ req)

private theorem node_of_cert (c : Cert) (s : Pair) (r : Nat) (hc : certOK c=true)
    (hk : c[key s]?=some r) : nodeOK c s r=true := by
  have h := (Std.HashMap.all_eq_true_iff_forall_mem_getElem.mp hc)
  have hm : key s ∈ c := Std.HashMap.mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some hk)
  have hv : c[key s]'hm=r := by
    have he := Std.HashMap.getElem?_eq_some_getElem hm
    rw [hk] at he
    exact Option.some.inj he.symm
  have hh := h (key s) hm
  rw [hv] at hh
  exact hh

private theorem child_of_check (c : Cert) (req shift : Nat) (s : Pair)
    (h : childOK c req shift s=true) : ∃ r, c[key s]?=some r ∧ r+shift≤req := by
  unfold childOK at h
  split at h
  next r he => exact ⟨r,he,of_decide_eq_true h⟩
  next => contradiction

/-- Finite DAG certificate: strictly decreasing precision requirements certify
    all branches without repeated traversal of common predecessors. -/
theorem cert_sound (reach : Nat → Nat → Prop)
    (parent : ∀ x y, 5<x → 8≤y → reach x y → ∃ a k, reach a k ∧ sectionPreimageCriterion a k x y)
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (c : Cert) (hc : certOK c=true) (req x y : Nat) (s : Pair)
    (hk : c[key s]?=some req) (hcon : congruent req x y s) : ¬reach x y := by
  induction req using Nat.strongRecOn generalizing s x y with
  | ind req ih =>
    have h := node_of_cert c s req hc hk
    simp only [nodeOK,Bool.and_eq_true,Bool.or_eq_true] at h
    obtain ⟨hs,hrest⟩ := h
    rcases hrest with hl | ⟨⟨hv,hd⟩,hh⟩
    · exact bad_sound reach forbid req x y s hs hcon hl
    · intro hr
      obtain ⟨hb,hx,hy,_⟩ := small_bounds req x y s hs hcon
      obtain ⟨hval,hgt⟩ := actual_valuation req x y s hs hcon hv
      obtain ⟨hvb,_⟩ := of_decide_eq_true hv
      obtain ⟨a,k,hp,he⟩ := parent x y hx hy hr
      obtain ⟨hpx,hpy,hpo⟩ := parity_match req x y s hb hcon
      rcases parent_equations a k x y (val s) hy hval hgt he with hdir | hhigh
      · obtain ⟨hye,ha,hk'⟩ := hdir
        have hy0 : s.y%2=0 := by omega
        simp only [hy0,ite_true] at hd
        obtain ⟨r,hrc,hrb⟩ := child_of_check c req 1 (dir s) hd
        have hcon' := direct_lift req x y a k s hb hcon hye ha hk'
        exact ih r (by omega) a k (dir s) hrc
          ⟨weaken _ _ _ (by omega) hcon'.1,weaken _ _ _ (by omega) hcon'.2⟩ hp
      · obtain ⟨n,hn,hpar,ha,hk'⟩ := hhigh
        have hn' : n∈List.range (val s+1) := List.mem_range.mpr (by omega)
        have hchk := (List.all_eq_true.mp hh) n hn'
        have hdepth : depthOK s n=true := decide_eq_true ⟨hn,by omega⟩
        simp only [hdepth,ite_true,Bool.and_eq_true] at hchk
        obtain ⟨r,hrc,hrb⟩ := child_of_check c req (n+2) (hi s n) hchk.2
        have hcon' := high_lift req x y a k n s hb (by omega) hcon hchk.1 ha hk'
        exact ih r (by omega) a k (hi s n) hrc
          ⟨weaken _ _ _ (by omega) hcon'.1,weaken _ _ _ (by omega) hcon'.2⟩ hp

def children (s : Pair) : List (Nat × Pair) :=
  (if s.y%2=0 then [(1,dir s)] else []) ++
  (List.range (val s+1)).filterMap (fun n => if depthOK s n then some (n+2,hi s n) else none)

def baseReq (s : Pair) : Nat := (2*(s.x+s.y+8)).log2+1

def build : Nat → Pair → Cert → Option (Nat × Cert)
  | 0,_,_ => none
  | f+1,s,c => match c[key s]? with
    | some req => some (req,c)
    | none => if bad s then
        let req := baseReq s
        some (req,c.insert (key s) req)
      else do
        let (req,c') ← (children s).foldlM (fun (req,c') (shift,p) => do
          let (r,c'') ← build f p c'
          pure (max req (r+shift),c'')) (max (baseReq s) (val s+1),c)
        pure (req,c'.insert (key s) req)

def runCert (f z : Nat) : Bool :=
  let s := lowShadow z
  match build f s {} with
  | none => false
  | some (r,c) => decide (r≤1024*z+129) && certOK c && c[key s]? == some r

theorem runCert_sound (reach : Nat → Nat → Prop)
    (parent : ∀ x y, 5<x → 8≤y → reach x y → ∃ a k, reach a k ∧ sectionPreimageCriterion a k x y)
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (f z u : Nat) (h : runCert f z=true) (hu : u+6*z+1=2^(1024*z+129)) :
    ¬reach (180*u+28) (166*u+25) := by
  cases he : build f (lowShadow z) {} with
  | none => simp [runCert,he] at h
  | some p =>
    rcases p with ⟨r,c⟩
    simp only [runCert,he,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
    have hc := lowShadow_congruent z u hu
    exact cert_sound reach parent forbid c h.1.2 r _ _ (lowShadow z) h.2
      ⟨weaken _ _ _ h.1.1 hc.1,weaken _ _ _ h.1.1 hc.2⟩

theorem low_shadow_stop_excluded (f z m k : Nat)
    (hm : m=512*z+67) (hstop : k+3*m+4=2^(2*m+3))
    (h : runCert f z=true) : ¬ BB6.Agent3.CReach 1 k := by
  obtain ⟨u,hk,hu⟩ := stopping_payload z m k hm hstop
  intro hr
  rw [hk] at hr
  have hR := BB6.Agent13One307.four_step_to_rectangle u hr
  apply runCert_sound BB6.Agent3.CReach ?_ BB6.Agent13TwoParent.odd_forbidden_image f z u h hu hR
  intro x y hx hy hReach
  obtain ⟨a,k,hp,he⟩ := BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5 x y hx hReach
  exact ⟨a,k,hp,(complete_section_inverse a k x y (by omega)).mp he⟩

#print axioms check_sound
#print axioms cert_sound
#print axioms runCert_sound
#print axioms lowShadow_congruent
#print axioms low_shadow_stop_excluded
#eval ((List.range 1000).filter (runCert 2000)).length
end BB6.Agent13NegativeShadow
