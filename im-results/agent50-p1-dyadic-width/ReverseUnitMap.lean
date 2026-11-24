import Lean

/-! Unit-cost modular embedding of the P1 scalar reverse-parent relation. -/
namespace BB6P1Unit

def unit (q d : Nat) : Nat := (2 * d) % (q + 1)
def bit (q d : Nat) : Nat := if q + 1 ≤ 2 * d then 1 else 0

def run (q d : Nat) : Nat → Nat
  | 0 => d
  | k+1 => unit (q+k) (run q d k)

def word (q d : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => 2 * word q d k + bit (q+k) (run q d k)

def moment (q d : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => 2 * moment q d k + (k+1) * bit (q+k) (run q d k)

theorem run_lt (q d k : Nat) (h : d < q) : run q d k < q+k := by
  cases k with
  | zero => simpa [run] using h
  | succ k =>
    simp only [run, unit]
    exact Nat.mod_lt _ (by omega)

theorem unit_equation (q d : Nat) (h : d < q) :
    2*d = unit q d + (q+1)*bit q d := by
  by_cases ht : q+1 ≤ 2*d
  · have hlt : 2*d-(q+1) < q+1 := by omega
    have hm : (2*d) % (q+1) = 2*d-(q+1) := by
      rw [Nat.mod_eq_sub_mod ht, Nat.mod_eq_of_lt hlt]
    simp [unit, bit, ht, hm]
  · have hlt : 2*d < q+1 := by omega
    simp [unit, bit, ht, Nat.mod_eq_of_lt hlt]

theorem run_add (q d i j : Nat) :
    run q d (i+j) = run (q+i) (run q d i) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have he : i+(j+1) = (i+j)+1 := by omega
    rw [he, run, run, ih]
    congr 1 <;> omega

theorem word_identity (q d k : Nat) (h : d < q) :
    2^k*d = run q d k + q*word q d k + moment q d k := by
  induction k with
  | zero => simp [run, word, moment]
  | succ k ih =>
    have he := unit_equation (q+k) (run q d k) (run_lt q d k h)
    have hdist : (q+k+1)*bit (q+k) (run q d k) =
        q*bit (q+k) (run q d k) + (k+1)*bit (q+k) (run q d k) := by
      rw [← Nat.add_mul]
      congr 1 <;> omega
    have hmul : 2^(k+1)*d = 2*(2^k*d) := by rw [Nat.pow_succ]; ac_rfl
    rw [hmul, ih, run, word, moment]
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_add]
    have ha : q * (2 * word q d k) = 2 * (q*word q d k) := by ac_rfl
    rw [ha]
    omega

def admissible (q d k : Nat) : Prop :=
  0 < k ∧ q+k ≤ 2^k*d ∧ 2^k*d+8 ≤ 2*(q+k)

-- Once the doubled value reaches the moving modulus, any later candidate
-- would exceed the upper margin of a legal scalar reverse parent.
theorem pow_growth (a r : Nat) (ha : 1 ≤ a) (hr : 1 ≤ r) :
    2*(a+r) ≤ 2^r*a+2 := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases h0 : r=0
    · subst r; simp; omega
    · have hp := ih (by omega)
      rw [Nat.pow_succ]
      have hx : 2^r*2*a = 2*(2^r*a) := by ac_rfl
      rw [hx]
      omega

theorem no_early_cross (q d k j : Nat) (hq : 0 < q)
    (h : admissible q d k) (hj : j < k) : 2^j*d < q+j := by
  apply Nat.lt_of_not_ge
  intro hge
  let r := k-j
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hsum : j+r=k := by dsimp [r]; omega
  have hg := pow_growth (q+j) r (by omega) hr
  have hm := Nat.mul_le_mul_left (2^r) hge
  have hp : 2^r*(2^j*d) = 2^k*d := by
    rw [← Nat.mul_assoc, ← Nat.pow_add]
    have : r+j=k := by omega
    rw [this]
  rw [hp] at hm
  rcases h with ⟨_, _, hu⟩
  omega

theorem run_before_edge (q d k j : Nat) (hq : 0 < q)
    (h : admissible q d k) (hj : j < k) : run q d j = 2^j*d := by
  induction j with
  | zero => simp [run]
  | succ j ih =>
    have hj' : j < k := by omega
    have hn := no_early_cross q d k (j+1) hq h hj
    rw [Nat.pow_succ] at hn ⊢
    simp only [run, unit, ih hj']
    have hh : 2*(2^j*d) = 2^j*2*d := by ac_rfl
    rw [hh, Nat.mod_eq_of_lt (by omega : 2^j*2*d < q+j+1)]

theorem edge_run (q d k : Nat) (hq : 0 < q)
    (h : admissible q d k) : run q d k = 2^k*d-(q+k) := by
  cases k with
  | zero => simp [admissible] at h
  | succ j =>
    have hb := run_before_edge q d (j+1) j hq h (by omega)
    have hl := h.2.1
    have hu := h.2.2
    rw [Nat.pow_succ] at hl hu ⊢
    simp only [run, unit, hb]
    have hh : 2*(2^j*d) = 2^j*2*d := by ac_rfl
    rw [hh, Nat.mod_eq_sub_mod (by omega : q+j+1 ≤ 2^j*2*d)]
    rw [Nat.mod_eq_of_lt (by omega : 2^j*2*d-(q+j+1) < q+j+1)]
    rw [Nat.add_assoc]

inductive Path : Nat → Nat → Nat → Nat → Prop
  | nil (q d : Nat) : Path q d 0 d
  | cons (q d k t e : Nat) (h : admissible q d k)
      (ht : Path (q+k) (2^k*d-(q+k)) t e) : Path q d (k+t) e

theorem path_run {q d t e : Nat} (h : Path q d t e) (hq : 0 < q) :
    run q d t = e := by
  induction h with
  | nil => rfl
  | cons q d k t e h ht ih =>
    rw [run_add, edge_run q d k hq h]
    exact ih (by omega)

theorem run_zero_prefix (q d k : Nat) (h : d < q)
    (hz : ∀ j < k, bit (q+j) (run q d j) = 0) :
    run q d k = 2^k*d := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
    have hpre := ih (fun j hj => hz j (by omega))
    have he := unit_equation (q+k) (run q d k) (run_lt q d k h)
    rw [hz k (by omega)] at he
    simp only [Nat.mul_zero, Nat.add_zero] at he
    rw [run, ← he, hpre, Nat.pow_succ]
    ac_rfl

theorem first_cross_edge (q d k : Nat) (h : d < q)
    (hz : ∀ j < k, bit (q+j) (run q d j) = 0)
    (hc : bit (q+k) (run q d k) = 1)
    (hm : run q d (k+1)+8 ≤ q+k+1) :
    admissible q d (k+1) := by
  have he := unit_equation (q+k) (run q d k) (run_lt q d k h)
  rw [hc, Nat.mul_one] at he
  have hu : unit (q+k) (run q d k) = run q d (k+1) := rfl
  rw [hu, run_zero_prefix q d k h hz] at he
  have hp : 2*(2^k*d) = 2^(k+1)*d := by rw [Nat.pow_succ]; ac_rfl
  rw [hp] at he
  unfold admissible
  omega

theorem path_append {q d i e : Nat} (h : Path q d i e)
    {j f : Nat} (ht : Path (q+i) e j f) : Path q d (i+j) f := by
  induction h with
  | nil q d => simpa using ht
  | cons q d k t e h hp ih =>
    have ht' : Path (q+k+t) e j f := by simpa [Nat.add_assoc] using ht
    have hh := Path.cons q d k (t+j) f h (ih ht')
    simpa [Nat.add_assoc] using hh

-- For an arbitrary guarded unit prefix, the last one-bit marks an exact
-- scalar reverse-parent path; its trailing zero bits are a partial edge.
theorem guarded_prefix (q d k : Nat) (h : d < q)
    (hm : ∀ j < k, bit (q+j) (run q d j) = 1 →
      run q d (j+1)+8 ≤ q+j+1) :
    ∃ l ≤ k, Path q d l (run q d l) ∧
      ∀ j, l ≤ j → j < k → bit (q+j) (run q d j) = 0 := by
  induction k with
  | zero => exact ⟨0, by omega, Path.nil q d, by omega⟩
  | succ k ih =>
    obtain ⟨l, hl, hp, hz⟩ := ih (fun j hj => hm j (by omega))
    by_cases hc : bit (q+k) (run q d k) = 1
    · let r := k-l
      have heq : l+r=k := by dsimp [r]; omega
      have h0 : run q d l < q+l := run_lt q d l h
      have hz' : ∀ j < r, bit (q+l+j) (run (q+l) (run q d l) j) = 0 := by
        intro j hj
        rw [← run_add, Nat.add_assoc]
        exact hz (l+j) (by omega) (by omega)
      have hc' : bit (q+l+r) (run (q+l) (run q d l) r) = 1 := by
        rw [← run_add, Nat.add_assoc, heq]
        exact hc
      have hm' : run (q+l) (run q d l) (r+1)+8 ≤ q+l+r+1 := by
        rw [← run_add, ← Nat.add_assoc l r 1, heq, Nat.add_assoc q l r, heq]
        exact hm k (by omega) hc
      have ha := first_cross_edge (q+l) (run q d l) r h0 hz' hc' hm'
      have hend := edge_run (q+l) (run q d l) (r+1) (by omega) ha
      have hstep : Path (q+l) (run q d l) (r+1)
          (run (q+l) (run q d l) (r+1)) := by
        rw [hend]
        have hs := Path.cons (q+l) (run q d l) (r+1) 0 _ ha (Path.nil _ _)
        simpa using hs
      have hpath := path_append hp hstep
      rw [← run_add, ← Nat.add_assoc l r 1, heq] at hpath
      exact ⟨k+1, by omega, hpath, by omega⟩
    · have hcz : bit (q+k) (run q d k) = 0 := by
        by_cases hle : q+k+1 ≤ 2*run q d k
        · simp [bit, hle] at hc
        · simp [bit, hle]
      refine ⟨l, by omega, hp, ?_⟩
      intro j hj hlt
      by_cases he : j=k
      · simpa [he] using hcz
      · exact hz j hj (by omega)

#print axioms word_identity
#print axioms no_early_cross
#print axioms edge_run
#print axioms path_run
#print axioms first_cross_edge
#print axioms guarded_prefix
end BB6P1Unit
