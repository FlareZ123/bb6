import AffineConeLowStop
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 1000000
namespace BB6.Agent15RationalShadow211
open BB6.Agent13AffineCone BB6.Agent46

structure Shadow where
  x : Nat
  y : Nat
  deriving Repr, DecidableEq

def parity (s : Shadow) : Nat := (s.x+s.y)%2
def q (s : Shadow) : Nat := s.x+s.y-211*parity s
def val (s : Shadow) : Nat := v2Aux ((q s).log2+1) (q s)
def small (b : Nat) (s : Shadow) : Bool := decide (0<s.x ∧ 0<s.y ∧ (212*(s.x+s.y+1688)).log2<b)
def bad (s : Shadow) : Bool := decide (s.y%2=1 ∧ ((s.x+s.y)%4=1 ∨ (s.x+s.y)%4=2))
def validVal (b : Nat) (s : Shadow) : Bool := decide (val s+1≤b ∧ q s%2^(val s+1)=2^val s ∧ 211*parity s≤s.x+s.y)
def dir (s : Shadow) : Shadow := ⟨s.x+s.y+422,(s.y+422)/2⟩
def hi (s : Shadow) (n : Nat) : Shadow :=
  let a := q s/2^(n+1)+211*(2+parity s)
  ⟨a,(s.x+2*s.y+211*(7+3*n)-a)/2⟩
def validHi (s : Shadow) (n : Nat) : Bool := decide (
  2^(n+1)*(hi s n).x=q s+2^(n+1)*(211*(2+parity s)) ∧
  2*(hi s n).y+(hi s n).x=s.x+2*s.y+211*(7+3*n))
def depthOK (s : Shadow) (n : Nat) : Bool := decide (n+2≤val s ∧ n%2=(s.x+1+parity s)%2)

def check : Nat → Nat → Shadow → Bool
  | 0,b,s => small b s && bad s
  | f+1,b,s => small b s && (bad s || (validVal b s &&
    (if s.y%2=0 then check f (b-1) (dir s) else true) &&
    (List.range (val s+1)).all (fun n => if depthOK s n then
      validHi s n && check f (b-(n+2)) (hi s n) else true)))

def congruent (b x y : Nat) (s : Shadow) : Prop :=
  2^b∣211*x+s.x ∧ 2^b∣211*y+s.y

private theorem weaken (b c p : Nat) (hcb : c≤b) (h : 2^b∣p) : 2^c∣p :=
  Nat.dvd_trans (Nat.pow_dvd_pow 2 hcb) h

private theorem cancel_pow (b r p : Nat) (hr : r≤b) (h : 2^b∣2^r*p) : 2^(b-r)∣p := by
  apply Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos (by decide : 0<(2:Nat)))
  rw [Nat.mul_comm (2^r) (2^(b-r)),Nat.pow_sub_mul_pow 2 hr]
  exact h

private theorem cancel211 (b z : Nat) (h : 2^b∣211*z) : 2^b∣z :=
  (Nat.Coprime.pow_left b (by decide : Nat.Coprime 2 211)).dvd_of_dvd_mul_left h

private theorem small_bounds (b x y : Nat) (s : Shadow)
    (hs : small b s=true) (hc : congruent b x y s) :
    2≤b ∧ 5<x ∧ 8≤y ∧ 212*(s.x+s.y+1688)<2^b := by
  obtain ⟨hx,hy,hl⟩ := of_decide_eq_true hs
  have hp := (Nat.log2_lt (by omega : 212*(s.x+s.y+1688)≠0)).mp hl
  have hb : 2≤b := by
    by_cases h : 2≤b
    · exact h
    · have hh : 2^b≤2^1 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  have hx' := Nat.le_of_dvd (by omega : 0<211*x+s.x) hc.1
  have hy' := Nat.le_of_dvd (by omega : 0<211*y+s.y) hc.2
  exact ⟨hb,by omega,by omega,hp⟩

private theorem parity_match (b x y : Nat) (s : Shadow) (hb : 2≤b) (h : congruent b x y s) :
    x%2=s.x%2 ∧ y%2=s.y%2 ∧ (x+y)%2=parity s := by
  have hx := Nat.mod_eq_zero_of_dvd (weaken b 1 (211*x+s.x) (by omega) h.1)
  have hy := Nat.mod_eq_zero_of_dvd (weaken b 1 (211*y+s.y) (by omega) h.2)
  change (211*x+s.x)%2=0 at hx
  change (211*y+s.y)%2=0 at hy
  unfold parity
  omega

private theorem bad_sound (reach : Nat → Nat → Prop)
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (b x y : Nat) (s : Shadow) (hs : small b s=true) (h : congruent b x y s) (hd : bad s=true) : ¬reach x y := by
  obtain ⟨hb,_,hy,_⟩ := small_bounds b x y s hs h
  obtain ⟨hy2,hm⟩ := of_decide_eq_true hd
  have hx4 := Nat.mod_eq_zero_of_dvd (weaken b 2 (211*x+s.x) hb h.1)
  have hy4 := Nat.mod_eq_zero_of_dvd (weaken b 2 (211*y+s.y) hb h.2)
  change (211*x+s.x)%4=0 at hx4
  change (211*y+s.y)%4=0 at hy4
  exact forbid x y (by omega) (by omega) (by omega)

private theorem actual_valuation (b x y : Nat) (s : Shadow)
    (hs : small b s=true) (hc : congruent b x y s) (hv : validVal b s=true) :
    (x+y+(x+y)%2)%2^(val s+1)=2^val s ∧ 2^val s<x+y+(x+y)%2 := by
  obtain ⟨hb,hx,hy,hbig⟩ := small_bounds b x y s hs hc
  obtain ⟨hvb,hvq,hqsub⟩ := of_decide_eq_true hv
  obtain ⟨_,_,ho⟩ := parity_match b x y s hb hc
  let Q := x+y+(x+y)%2
  let v := val s
  have hsum : 2^b∣211*Q+q s := by
    have hh := Nat.dvd_add hc.1 hc.2
    unfold Q q
    rw [ho]
    rw [show 211*(x+y+parity s)+(s.x+s.y-211*parity s)=(211*x+s.x)+(211*y+s.y) by omega]
    exact hh
  have hp : 2^v∣2^(v+1) := Nat.pow_dvd_pow 2 (by omega)
  have hqdiv : 2^v∣q s := by
    apply Nat.dvd_of_mod_eq_zero
    rw [←Nat.mod_mod_of_dvd (q s) hp]
    change q s%2^(val s+1)%2^val s=0
    rw [hvq,Nat.mod_self]
  have hprod : 2^v∣211*Q := by
    have h := Nat.dvd_sub (weaken b v _ (by omega) hsum) hqdiv
    simpa using h
  obtain ⟨j,hj⟩ := cancel211 v Q hprod
  have hnot : ¬ 2^(v+1)∣Q := by
    intro h
    have hd : 2^(v+1)∣211*Q := Nat.dvd_trans h (Nat.dvd_mul_left Q 211)
    have hq := Nat.dvd_sub (weaken b (v+1) _ hvb hsum) hd
    have hq' : 2^(v+1)∣q s := by
      rwa [show 211*Q+q s-211*Q=q s by omega] at hq
    have hz : q s%2^(v+1)=0 := Nat.mod_eq_zero_of_dvd hq'
    change q s%2^(val s+1)=0 at hz
    rw [hvq] at hz
    exact (Nat.ne_of_gt (Nat.pow_pos (by decide : 0<(2:Nat)))) hz
  have hodd : j%2=1 := by
    by_cases hn : j%2=1
    · exact hn
    · have he : 2∣j := Nat.dvd_of_mod_eq_zero (by omega)
      exfalso
      apply hnot
      rw [hj,Nat.pow_succ]
      exact Nat.mul_dvd_mul_left _ he
  have hqge : 2^v≤q s := by
    have h := Nat.mod_le (q s) (2^(v+1))
    change q s%2^(val s+1)≤q s at h
    rw [hvq] at h
    exact h
  have hqle : q s≤s.x+s.y := Nat.sub_le _ _
  have htot := Nat.le_of_dvd (by omega : 0<211*Q+q s) hsum
  constructor
  · change Q%2^(v+1)=2^v
    rw [hj,Nat.pow_succ,Nat.mul_mod_mul_left,hodd,Nat.mul_one]
  · change 2^v<Q
    omega

private theorem direct_lift (b x y a k : Nat) (s : Shadow) (hb : 2≤b)
    (hc : congruent b x y s) (hy : y%2=0)
    (ha : a+2=x+y) (hk : 2*k+2=y) : congruent (b-1) a k (dir s) := by
  obtain ⟨_,hsy,_⟩ := parity_match b x y s hb hc
  have he : s.y%2=0 := by omega
  have h1 : 211*a+(dir s).x=(211*x+s.x)+(211*y+s.y) := by unfold dir; dsimp; omega
  have h2 : 2*(211*k+(dir s).y)=211*y+s.y := by unfold dir; dsimp; omega
  constructor
  · rw [h1]; exact weaken b (b-1) _ (by omega) (Nat.dvd_add hc.1 hc.2)
  · have hh : 2^b∣2^1*(211*k+(dir s).y) := by rw [Nat.pow_one,h2]; exact hc.2
    exact cancel_pow b 1 _ (by omega) hh

private theorem high_lift (b x y a k n : Nat) (s : Shadow)
    (hb : 2≤b) (hn : n+2≤b) (hc : congruent b x y s)
    (hqsub : 211*parity s≤s.x+s.y)
    (hvalid : validHi s n=true)
    (ha : x+y+(x+y)%2=2^(n+1)*(a+2+(x+y)%2))
    (hk : 2*k+a+7+3*n=x+2*y) : congruent (b-(n+2)) a k (hi s n) := by
  obtain ⟨_,_,ho⟩ := parity_match b x y s hb hc
  obtain ⟨hA,hK⟩ := of_decide_eq_true hvalid
  have he : q s+211*parity s=s.x+s.y := by unfold q; omega
  have haD := congrArg (fun z : Nat => 211*z) ha
  simp only [ho] at haD
  rw [Nat.mul_left_comm 211 (2^(n+1))] at haD
  simp only [Nat.mul_add] at haD hA
  have hsum : 2^(n+1)*(211*a+(hi s n).x)=(211*x+s.x)+(211*y+s.y) := by
    simp only [Nat.mul_add]
    omega
  have h1 : 2^(b-(n+1))∣211*a+(hi s n).x := by
    apply cancel_pow b (n+1) _ (by omega)
    rw [hsum]
    exact Nat.dvd_add hc.1 hc.2
  have hsum2 : 2*(211*k+(hi s n).y)+(211*a+(hi s n).x)=(211*x+s.x)+2*(211*y+s.y) := by omega
  have h2 : 2^b∣2*(211*k+(hi s n).y)+(211*a+(hi s n).x) := by
    rw [hsum2]
    apply Nat.dvd_add hc.1
    exact Nat.dvd_trans hc.2 (Nat.dvd_mul_left _ _)
  have h3 := weaken b (b-(n+1)) _ (by omega) h2
  have h4 : 2^(b-(n+1))∣2*(211*k+(hi s n).y) := by
    have hsub := Nat.dvd_sub h3 h1
    rw [Nat.add_sub_cancel] at hsub
    exact hsub
  have h5 := cancel_pow (b-(n+1)) 1 (211*k+(hi s n).y) (by omega) (by simpa using h4)
  constructor
  · exact weaken _ _ _ (by omega) h1
  · rwa [show b-(n+1)-1=b-(n+2) by omega] at h5

/-- Odd-denominator negative-shadow certificate: 211-scaled numerators,
    no large positive counters need to be constructed. -/
theorem check_sound (reach : Nat → Nat → Prop)
    (parent : ∀ x y, 5<x → 8≤y → reach x y → ∃ a k, reach a k ∧ sectionPreimageCriterion a k x y)
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (f b x y : Nat) (s : Shadow) (h : check f b s=true) (hc : congruent b x y s) : ¬reach x y := by
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
      obtain ⟨hvb,_,hqsub⟩ := of_decide_eq_true hv
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
          (high_lift b x y a k n s hb (by omega) hc hqsub hchk.1 ha hk) hp

def u5Shadow (w : Nat) : Shadow := ⟨44*(1360+22155*w)+211,42*(1360+22155*w)+211⟩
def u5Check (f w : Nat) : Bool := check f (201+3360*w) (u5Shadow w)

theorem u5_congruent (w t : Nat) (ht : 1≤t)
    (h : 211*t+1360+22155*w=20*2^(201+3360*w)) :
    congruent (201+3360*w) (44*t-1) (42*t-1) (u5Shadow w) := by
  constructor
  · refine ⟨880,?_⟩
    unfold u5Shadow; dsimp
    omega
  · refine ⟨840,?_⟩
    unfold u5Shadow; dsimp
    omega

theorem u5_shadow_x_excluded (f w t : Nat) (ht : 1≤t)
    (h : 211*t+1360+22155*w=20*2^(201+3360*w))
    (hc : u5Check f w=true) : ¬BB6.Agent3.CReach (44*t-1) (42*t-1) := by
  apply check_sound BB6.Agent3.CReach ?_ BB6.Agent13TwoParent.odd_forbidden_image f (201+3360*w)
    _ _ (u5Shadow w) hc (u5_congruent w t ht h)
  intro x y hx hy hr
  obtain ⟨a,k,hp,hedge⟩ := BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5 x y hx hr
  exact ⟨a,k,hp,(complete_section_inverse a k x y (by omega)).mp hedge⟩

private theorem affine_mod (m a c w z : Nat) (h : w%m=z%m) :
    (a*w+c)%m=(a*z+c)%m := by
  rw [Nat.add_mod,Nat.mul_mod,h]
  rw [Nat.add_mod (a*z) c m,Nat.mul_mod a z m]

private theorem u5Shadow_mod (b w z : Nat) (h : w%2^b=z%2^b) :
    (u5Shadow w).x%2^b=(u5Shadow z).x%2^b ∧
    (u5Shadow w).y%2^b=(u5Shadow z).y%2^b := by
  unfold u5Shadow
  have hx (u : Nat) : 44*(1360+22155*u)+211=974820*u+60051 := by omega
  have hy (u : Nat) : 42*(1360+22155*u)+211=930510*u+57331 := by omega
  simp only [hx,hy]
  exact ⟨affine_mod _ _ _ _ _ h,affine_mod _ _ _ _ _ h⟩

/-- Transfer a single small rational shadow to its whole residue cylinder,
    keeping the true exponent guard explicit. -/
theorem u5_congruent_cylinder (b w z t : Nat) (ht : 1≤t)
    (hb : b≤201+3360*w) (hw : w%2^b=z%2^b)
    (h : 211*t+1360+22155*w=20*2^(201+3360*w)) :
    congruent b (44*t-1) (42*t-1) (u5Shadow z) := by
  have hc := u5_congruent w t ht h
  obtain ⟨hx,hy⟩ := u5Shadow_mod b w z hw
  have hxx : 2^b∣211*(44*t-1)+(u5Shadow w).x :=
    Nat.dvd_trans (Nat.pow_dvd_pow 2 hb) hc.1
  have hyy : 2^b∣211*(42*t-1)+(u5Shadow w).y :=
    Nat.dvd_trans (Nat.pow_dvd_pow 2 hb) hc.2
  constructor
  · apply Nat.dvd_of_mod_eq_zero
    have hh := Nat.mod_eq_zero_of_dvd hxx
    rw [Nat.add_mod,hx] at hh
    rw [Nat.add_mod]
    exact hh
  · apply Nat.dvd_of_mod_eq_zero
    have hh := Nat.mod_eq_zero_of_dvd hyy
    rw [Nat.add_mod,hy] at hh
    rw [Nat.add_mod]
    exact hh

theorem u5_shadow_x_excluded_cylinder (f b w z t : Nat) (ht : 1≤t)
    (hb : b≤201+3360*w) (hw : w%2^b=z%2^b)
    (h : 211*t+1360+22155*w=20*2^(201+3360*w))
    (hc : check f b (u5Shadow z)=true) : ¬BB6.Agent3.CReach (44*t-1) (42*t-1) := by
  apply check_sound BB6.Agent3.CReach ?_ BB6.Agent13TwoParent.odd_forbidden_image f b
    _ _ (u5Shadow z) hc (u5_congruent_cylinder b w z t ht hb hw h)
  intro x y hx hy hr
  obtain ⟨a,k,hp,hedge⟩ := BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5 x y hx hr
  exact ⟨a,k,hp,(complete_section_inverse a k x y (by omega)).mp hedge⟩

#print axioms u5_shadow_x_excluded_cylinder

#print axioms u5_shadow_x_excluded
end BB6.Agent15RationalShadow211
