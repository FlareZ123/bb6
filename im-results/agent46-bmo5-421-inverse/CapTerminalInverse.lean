import CapCanonicalEntry

namespace CapSieve

/-- Reduce along the same-band ray until there is no earlier band coordinate. -/
def reduceRay (k q : Nat) : Nat :=
  if q%3=0 ∧ 3*(k+6)≤q then reduceRay k (q/3) else q
termination_by q
decreasing_by omega

theorem reduce_ray_spec {k q : Nat} (h : PosQ k q) :
    CanonQ k (reduceRay k q) ∧ ∃ a, q=3^a*(reduceRay k q) := by
  rw [reduceRay]
  split
  next ht =>
    have he : 3*(q/3)=q := by omega
    have hsmall : PosQ k (q/3) := by
      unfold PosQ at *
      omega
    obtain ⟨hc,a,ha⟩ := reduce_ray_spec hsmall
    refine ⟨hc,a+1,?_⟩
    rw [Nat.pow_succ,show 3^a*3*(reduceRay k (q/3))=3*(3^a*(reduceRay k (q/3))) by ac_rfl,
      ←ha]
    omega
  next ht =>
    exact ⟨⟨h,by omega⟩,0,by simp⟩
termination_by q
decreasing_by omega

theorem terminal_weight_phase (n k w : Nat) (he : 3^n*w=2*(k+n)+3) :
    w%4=(2*k+3)%4 := by
  induction n generalizing k w with
  | zero => simp at he; omega
  | succ n ih =>
    have hh : 3^n*(3*w)=2*(k+1+n)+3 := by
      rw [←Nat.mul_assoc,←Nat.pow_succ]
      exact he.trans (by omega)
    have hp := ih (k+1) (3*w) hh
    omega

theorem terminal_weight_valid {k n w : Nat}
    (he : 3^n*w=2*(k+n)+3) : CapNegative.Valid k w := by
  have hp : 0<w := by
    by_cases h : w=0
    · simp [h] at he
    · omega
  have hb : w≤2*k+7 := by
    by_cases h : w≤2*k+7
    · exact h
    · have := CapNegative.above_grows (k:=k) (w:=w) (by omega) n
      omega
  exact ⟨hp,hb,terminal_weight_phase n k w he⟩

theorem band_scale_lower {k : Nat} (hk : 2≤k) :
    3*k+19≤2*P k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : 2≤k
    · have hh := ih h
      rw [p_succ]
      omega
    · have he : k=1 := by omega
      subst k
      unfold P
      decide

/-- The negative Q of any terminal candidate has a positive immediate
    same-band predecessor in every band k>=2. -/
theorem terminal_candidate_parent {k n w : Nat}
    (hk : 2≤k) (hphase : w%3=2^k%3) (he : 3^n*w=2*(k+n)+3) :
    PosQ k (negQ k w/3) ∧ 3*(negQ k w/3)=negQ k w := by
  have hval := terminal_weight_valid he
  have hq := negQ_valid hval
  have heq := negQ_eq hval
  have hp := band_scale_lower hk
  have hP := p_ge k
  have hmod : negQ k w%3=0 := by
    unfold P at heq
    omega
  have hmul : 3*(negQ k w/3)=negQ k w := by omega
  have hlo := hq.2
  have hhi := hq.1.2.1
  have hpar := hq.1.2.2
  exact ⟨⟨by omega,by omega,by omega⟩,hmul⟩

/-- Each terminal exponent gives exactly one canonical positive state,
    not merely a necessary condition, in bands k>=2. -/
theorem terminal_candidate_exact {k n : Nat} (hk : 2≤k)
    (hn : TerminalExponent k n) :
    ∃ q, CanonQ k q ∧ 3^n*(2*positiveNext k q-3)=2*(k+n)+3 ∧
      ∀ v, CanonQ k v → 3^n*(2*positiveNext k v-3)=2*(k+n)+3 → v=q := by
  obtain ⟨w,hw,hwphase,he⟩ := hn
  have hval := terminal_weight_valid he
  have hneg := negQ_valid hval
  obtain ⟨hpar,hmul⟩ := terminal_candidate_parent hk hwphase he
  let q := reduceRay k (negQ k w/3)
  obtain ⟨hcan,a,ha⟩ := reduce_ray_spec hpar
  change CanonQ k q at hcan
  change negQ k w/3=3^a*q at ha
  have hwindow : 3^a*q≤2*P k-2 ∧ 2*P k-2<3^(a+1)*q := by
    have hhi := hpar.2.1
    have hx := hneg.2
    rw [ha] at hhi hmul
    refine ⟨hhi,?_⟩
    calc
      2*P k-2 < negQ k w := Nat.lt_of_lt_of_le (by have := p_ge k; omega) hx
      _ = 3*(3^a*q) := hmul.symm
      _ = 3^(a+1)*q := by rw [Nat.pow_succ]; ac_rfl
  have hqpos : 0<q := by have := hcan.1.1; omega
  have hcnt : positiveCount k q=a := by
    unfold positiveCount
    apply CapMacro.triple_window_unique hqpos
    · exact CapMacro.tripleCount_spec hqpos hcan.1.2.1
    · exact hwindow
  have hprod : positiveProduct k q=negQ k w := by
    unfold positiveProduct
    rw [hcnt,Nat.pow_succ,show 3^a*3*q=3*(3^a*q) by ac_rfl,←ha,hmul]
  have hp := positive_next_equation hqpos hcan.1.2.1
  have hqeq := negQ_eq hval
  have hw' : 2*positiveNext k q-3=w := by omega
  have hfinal : 3^n*(2*positiveNext k q-3)=2*(k+n)+3 := by rw [hw']; exact he
  refine ⟨q,hcan,hfinal,?_⟩
  intro v hv hh
  exact canonical_terminal_exponent_inj hv hcan hh hfinal

#print axioms reduce_ray_spec
#print axioms terminal_candidate_parent
#print axioms terminal_candidate_exact
end CapSieve
