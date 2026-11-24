import Lean

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CascadeResetShield

/-- Exact first-reset inverse grammar, parameterized independently for local
    kernel testing. The source adapter identifies this with ResetParent. -/
def Edge (h u : Nat) : Prop :=
  (∃ k, (6*2^k-1≤u ∧ u≤8*2^k-3) ∧ 2*u=8*2^k+h+k) ∨
  (∃ k t d, d%2=1 ∧ (6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1) ∧
    2*u+5=3^(t+1)*d ∧ 2*(2^t*d)=8*2^k+h+k+5)

/-- Check a proposed source level and drain valuation. Only successful
    edges are used in certificates, so the witness generator is untrusted. -/
def nextAt (h k t : Nat) : Option Nat :=
  let p := 2^k
  if (h+k)%2=0 then
    let u := 4*p+(h+k)/2
    if 6*p-1≤u ∧ u≤8*p-3 ∧ 2*u=8*p+h+k then some u else none
  else
    let d := (4*p+(h+k)/2+3)/2^t
    let u := (3^(t+1)*d-5)/2
    if d%2=1 ∧ 6*p+1≤2^t*d ∧ 2^t*d≤8*p-1 ∧
       2*u+5=3^(t+1)*d ∧ 2*(2^t*d)=8*p+h+k+5 then some u else none

theorem nextAt_sound (h k t u : Nat) (hs : nextAt h k t = some u) : Edge h u := by
  unfold nextAt at hs
  dsimp only at hs
  split at hs
  · split at hs
    · rename_i hc
      have he := Option.some.inj hs
      subst u
      exact Or.inl ⟨k, ⟨hc.1,hc.2.1⟩,hc.2.2⟩
    · contradiction
  · split at hs
    · rename_i hc
      have he := Option.some.inj hs
      subst u
      exact Or.inr ⟨k,t,_,hc.1,⟨hc.2.1,hc.2.2.1⟩,hc.2.2.2.1,hc.2.2.2.2⟩
    · contradiction

inductive Path (R : Nat → Nat → Prop) : Nat → Nat → Prop where
  | refl (x) : Path R x x
  | step {x y z} : R x y → Path R y z → Path R x z

theorem path_trans {R : Nat → Nat → Prop} {x y z : Nat}
    (h : Path R x y) (g : Path R y z) : Path R x z := by
  induction h with
  | refl => exact g
  | step he _ ih => exact Path.step he (ih g)

theorem path_mono {R : Nat → Nat → Prop}
    (hm : ∀ x y, R x y → x < y) {x y : Nat} (h : Path R x y) : x ≤ y := by
  induction h with
  | refl => omega
  | step he _ ih => exact Nat.le_trans (Nat.le_of_lt (hm _ _ he)) ih

/-- Compact certificate: each reset needs only its sweep level and drain
    valuation. No giant per-step height is supplied to the checker. -/
def runBlock : Nat → List (Nat × Nat) → Option Nat
  | h, [] => some h
  | h, (k,t)::rest =>
    match nextAt h k t with
    | none => none
    | some u => runBlock u rest

theorem runBlock_sound {R : Nat → Nat → Prop}
    (hedge : ∀ h u, Edge h u → R h u)
    (h u : Nat) (w : List (Nat × Nat)) (hc : runBlock h w = some u) : Path R h u := by
  induction w generalizing h with
  | nil =>
    simp [runBlock] at hc
    subst u
    exact Path.refl _
  | cons a rest ih =>
    rcases a with ⟨k,t⟩
    cases he : nextAt h k t with
    | none => simp [runBlock,he] at hc
    | some v =>
      have hs : runBlock v rest = some u := by simpa [runBlock,he] using hc
      exact Path.step (hedge _ _ (nextAt_sound _ _ _ _ he)) (ih _ hs)

/-- Fatal reset index recoverable exactly by the bit length (n≥2). -/
def fatal (n : Nat) : Nat := 4*2^n-n-4

theorem fatal_log2 (n : Nat) (hn : 2≤n) : (fatal n).log2 = n+1 := by
  have hp : n+4 ≤ 2^(n+1) := by
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases h : 2≤n
      · have hh := ih h
        rw [show n+1+1=n+1+1 by rfl, Nat.pow_succ]
        omega
      · have he : n=1 := by omega
        subst n
        decide
  have hpow : 2^(n+2)=4*2^n := by rw [Nat.pow_add]; omega
  have hpow' : 2^(n+1)=2*2^n := by rw [Nat.pow_succ]; omega
  have hlo : 2^(n+1) ≤ fatal n := by simp only [fatal]; omega
  have hhi : fatal n < 2^(n+2) := by simp only [fatal]; omega
  apply (Nat.log2_eq_iff (by omega)).mpr
  exact ⟨hlo,hhi⟩

theorem fatal_mono (n N : Nat) (hn : n≤N) : fatal n ≤ fatal N := by
  induction N with
  | zero =>
    have he : n=0 := by omega
    subst n
    exact Nat.le_refl _
  | succ N ih =>
    by_cases h : n≤N
    · apply Nat.le_trans (ih h)
      have hp : 1≤2^N := Nat.one_le_pow N 2 (by decide)
      simp only [fatal,Nat.pow_succ]
      omega
    · have he : n=N+1 := by omega
      subst n
      exact Nat.le_refl _

/-- Each successful reset input lies strictly between adjacent fatal heights. -/
theorem edge_source_interval (h u : Nat) (he : Edge h u) :
    ∃ k, fatal k < h ∧ h < fatal (k+1) := by
  have hbound (k : Nat) : k+4 ≤ 4*2^k := by
    induction k with
    | zero => decide
    | succ k ih => rw [Nat.pow_succ]; omega
  rcases he with ⟨k,⟨hl,hh⟩,hq⟩ | ⟨k,t,d,hd,⟨hl,hh⟩,hout,hq⟩
  · refine ⟨k,?_,?_⟩
    · have hb := hbound k
      have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
      simp only [fatal]
      omega
    · have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
      simp only [fatal,Nat.pow_succ]
      omega
  · refine ⟨k,?_,?_⟩
    · have hb := hbound k
      have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
      simp only [fatal]
      omega
    · have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
      simp only [fatal,Nat.pow_succ]
      omega

theorem fatal_dead (n u : Nat) : ¬ Edge (fatal n) u := by
  intro he
  obtain ⟨k,hl,hh⟩ := edge_source_interval _ _ he
  by_cases h : n≤k
  · have hm := fatal_mono n k h
    omega
  · have hm := fatal_mono (k+1) n (by omega)
    omega

/-- Strict increase and uniqueness of the executable reset relation are
    also consequences of the arithmetic grammar itself. -/
theorem edge_strict (h u : Nat) (he : Edge h u) : h<u := by
  rcases he with ⟨k,⟨hl,hh⟩,hq⟩ | ⟨k,t,d,hd,⟨hl,hh⟩,hout,hq⟩
  · have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
    omega
  · have hbase (t : Nat) : 3*2^t ≤ 3^(t+1) := by
      induction t with
      | zero => decide
      | succ t ih => rw [Nat.pow_succ,Nat.pow_succ]; omega
    have hm := Nat.mul_le_mul_right d (hbase t)
    have hc : 3*(2^t*d) ≤ 3^(t+1)*d := by
      simpa only [Nat.mul_assoc] using hm
    have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
    omega

private theorem odd_factor_unique (t s d e : Nat)
    (hd : d%2=1) (he : e%2=1) (h : 2^t*d=2^s*e) : t=s ∧ d=e := by
  induction t generalizing s d e with
  | zero =>
    cases s with
    | zero => simpa using h
    | succ s =>
      rw [Nat.pow_zero,Nat.one_mul,Nat.pow_succ] at h
      have hh : d=2*(2^s*e) := by rw [h]; ac_rfl
      omega
  | succ t ih =>
    cases s with
    | zero =>
      rw [Nat.pow_zero,Nat.one_mul,Nat.pow_succ] at h
      have hh : e=2*(2^t*d) := by rw [←h]; ac_rfl
      omega
    | succ s =>
      rw [Nat.pow_succ,Nat.pow_succ] at h
      have hh : 2*(2^t*d)=2*(2^s*e) := by
        calc
          2*(2^t*d) = (2^t*2)*d := by ac_rfl
          _ = (2^s*2)*e := h
          _ = 2*(2^s*e) := by ac_rfl
      obtain ⟨ht,hd'⟩ := ih s d e hd he (by omega)
      exact ⟨by omega,hd'⟩

private theorem interval_unique (h k l : Nat)
    (hkl : fatal k < h ∧ h < fatal (k+1))
    (hll : fatal l < h ∧ h < fatal (l+1)) : k=l := by
  by_cases he : k=l
  · exact he
  · by_cases ht : k<l
    · have hm := fatal_mono (k+1) l (by omega)
      omega
    · have hm := fatal_mono (l+1) k (by omega)
      omega

private theorem fatal_bound (k : Nat) : k+4 ≤ 4*2^k := by
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

private theorem even_interval (h u k : Nat)
    (hl : 6*2^k-1≤u) (hh : u≤8*2^k-3) (hq : 2*u=8*2^k+h+k) :
    fatal k < h ∧ h < fatal (k+1) := by
  have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
  have hb := fatal_bound k
  constructor <;> simp only [fatal,Nat.pow_succ] <;> omega

private theorem odd_interval (h k q : Nat)
    (hl : 6*2^k+1≤q) (hh : q≤8*2^k-1) (hq : 2*q=8*2^k+h+k+5) :
    fatal k < h ∧ h < fatal (k+1) := by
  have hb := fatal_bound k
  constructor <;> simp only [fatal,Nat.pow_succ] <;> omega

theorem edge_deterministic (h u v : Nat) (hu : Edge h u) (hv : Edge h v) : u=v := by
  rcases hu with ⟨k,⟨hl,hh⟩,hq⟩ | ⟨k,t,d,hd,⟨hl,hh⟩,hout,hq⟩ <;>
    rcases hv with ⟨l,⟨gl,gh⟩,gq⟩ | ⟨l,s,e,ge,⟨gl,gh⟩,gout,gq⟩
  · have hk := interval_unique h k l (even_interval h u k hl hh hq) (even_interval h v l gl gh gq)
    subst l
    omega
  · have hk := interval_unique h k l (even_interval h u k hl hh hq) (odd_interval h l _ gl gh gq)
    subst l
    omega
  · have hk := interval_unique h k l (odd_interval h k _ hl hh hq) (even_interval h v l gl gh gq)
    subst l
    omega
  · have hk := interval_unique h k l (odd_interval h k _ hl hh hq) (odd_interval h l _ gl gh gq)
    subst l
    obtain ⟨ht,he⟩ := odd_factor_unique t s d e hd ge (by omega)
    subst s
    subst e
    omega

/-- A deterministic increasing relation cannot visit a dead target below
    the endpoint of an accepted path. This removes all per-step fatal tests. -/
theorem path_excludes_dead {R : Nat → Nat → Prop}
    (hdet : ∀ x y z, R x y → R x z → y=z)
    (hmono : ∀ x y, R x y → x<y)
    {x z target : Nat} (hp : Path R x z) (hlt : target<z)
    (hdead : ∀ u, ¬ R target u) : ¬ Path R x target := by
  induction hp with
  | refl =>
    intro ht
    have hm := path_mono hmono ht
    omega
  | step he hp ih =>
    intro ht
    cases ht with
    | refl => exact hdead _ he
    | step he' ht =>
      have h := hdet _ _ _ he he'
      subst h
      exact ih hlt ht

/-- One actual successful prefix, extending beyond the largest fatal
    height in the range, rules out every bounded fatal index at all times. -/
theorem bounded_fatal_exclusion {R : Nat → Nat → Prop}
    (hdet : ∀ x y z, R x y → R x z → y=z)
    (hmono : ∀ x y, R x y → x<y)
    (hedge : ∀ h u, R h u → Edge h u)
    (N z : Nat) (hp : Path R 2 z) (hz : fatal N < z)
    (n : Nat) (hn : n≤N) : ¬ Path R 2 (fatal n) :=
  path_excludes_dead hdet hmono hp (Nat.lt_of_le_of_lt (fatal_mono n N hn) hz)
    (fun u he => fatal_dead n u (hedge _ _ he))

#print axioms nextAt_sound
#print axioms runBlock_sound
#print axioms bounded_fatal_exclusion
end CascadeResetShield
