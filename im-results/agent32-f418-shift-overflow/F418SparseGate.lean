import Init

/-! Exact cancellation-pivot decomposition of a signed sparse power queue.
The result depends only on the representation, not on a global bound on debt. -/
namespace BB6.Agent32F418.SparseGate

def mass (hs : List Nat) : Nat := (hs.map fun h => 2^h).sum

def NoEven (n : Nat) : Prop := ∀ i : Nat, i % 2 = 0 → n.testBit i = false

def Spaced (hs : List Nat) : Prop := hs.Pairwise (fun a b => a+4≤b)

@[simp] theorem mass_nil : mass [] = 0 := rfl
@[simp] theorem mass_cons (h : Nat) (hs : List Nat) :
    mass (h::hs) = 2^h+mass hs := rfl
@[simp] theorem mass_append (as bs : List Nat) :
    mass (as++bs) = mass as+mass bs := by simp [mass]

theorem mass_shift (k : Nat) (hs : List Nat) (hk : ∀ i ∈ hs, k ≤ i) :
    mass hs = 2^k * mass (hs.map (·-k)) := by
  induction hs with
  | nil => simp [mass]
  | cons a as ih =>
    have ha := hk a (by simp)
    have ht : ∀ i ∈ as, k ≤ i := by intro i hi; exact hk i (by simp [hi])
    simp only [List.map_cons,mass_cons]
    rw [ih ht,Nat.mul_add,←Nat.pow_add,show k+(a-k)=a by omega]

theorem mass_bits {hs : List Nat} (hp : hs.Pairwise (· < ·)) (i : Nat) :
    (mass hs).testBit i = decide (i ∈ hs) := by
  induction hs with
  | nil => simp [mass]
  | cons a as ih =>
    obtain ⟨ha,has⟩ := List.pairwise_cons.mp hp
    have hfact := mass_shift (a+1) as (by intro j hj; have hh := ha j hj; omega)
    have hsmall : 2^a < 2^(a+1) := Nat.pow_lt_pow_right (by decide) (by omega)
    have he : mass (a::as)=2^(a+1)*mass (as.map (·-(a+1)))+2^a := by
      rw [mass_cons,hfact]; omega
    rw [he,Nat.testBit_two_pow_mul_add _ hsmall]
    by_cases h : i<a+1
    · have hn : i ∉ as := by intro hi; have hh:=ha i hi; omega
      simp [h,Nat.testBit_two_pow,hn,eq_comm]
    · have hne : i≠a := by omega
      have ht : (mass as).testBit i = (mass (as.map (·-(a+1)))).testBit (i-(a+1)) := by
        rw [hfact,Nat.mul_comm,Nat.testBit_mul_two_pow]
        simp [show a+1≤i by omega]
      rw [if_neg h,←ht,ih has]
      simp [hne]

/-- The debt is paid by a unique first crossing source in the ordered queue.
All earlier sources have been absorbed; all later sources remain intact. -/
theorem crossing_exists (hs : List Nat) (d : Nat) (hd : 0<d) (hm : d≤mass hs) :
    ∃ pre a post, hs=pre++a::post ∧ mass pre<d ∧ d≤mass pre+2^a := by
  induction hs generalizing d with
  | nil => simp at hm; omega
  | cons a as ih =>
    by_cases h : d≤2^a
    · exact ⟨[],a,as,by simp,by simpa using hd,by simpa using h⟩
    · have hd' : 0<d-2^a := by omega
      have hm' : d-2^a≤mass as := by rw [mass_cons] at hm; omega
      obtain ⟨pre,b,post,he,hl,hu⟩ := ih (d-2^a) hd' hm'
      exact ⟨a::pre,b,post,by simp [he],by rw [mass_cons]; omega,by rw [mass_cons]; omega⟩

theorem crossing_remainder {pre post : List Nat} {a d : Nat}
    (hl : mass pre<d) (hu : d≤mass pre+2^a) :
    mass (pre++a::post)-d = (mass pre+2^a-d)+mass post ∧
      mass pre+2^a-d < 2^a := by
  simp only [mass_append,mass_cons]
  omega

/-- A low remainder and separated higher powers have exactly disjoint bits. -/
theorem remainder_bits {r a : Nat} {post : List Nat}
    (hr : r<2^a) (hp : post.Pairwise (· < ·))
    (hh : ∀ i∈post, a≤i) (i : Nat) :
    (r+mass post).testBit i = if i<a then r.testBit i else decide (i∈post) := by
  have hfact := mass_shift a post hh
  have he : r+mass post = 2^a*mass (post.map (·-a))+r := by rw [hfact]; omega
  rw [he,Nat.testBit_two_pow_mul_add _ hr]
  by_cases hi : i<a
  · simp [hi]
  · have ht : (mass post).testBit i = (mass (post.map (·-a))).testBit (i-a) := by
      rw [hfact,Nat.mul_comm,Nat.testBit_mul_two_pow]
      simp [show a≤i by omega]
    rw [if_neg hi,←ht,mass_bits hp]; simp [hi]

/-- Exact gate criterion, rather than a one-sided high-bit exclusion. -/
theorem noEven_remainder_iff {r a : Nat} {post : List Nat}
    (hr : r<2^a) (hp : post.Pairwise (· < ·)) (hh : ∀ i∈post, a≤i) :
    NoEven (r+mass post) ↔ NoEven r ∧ ∀ i∈post, i%2=1 := by
  constructor
  · intro h
    constructor
    · intro i hi
      by_cases hia : i<a
      · have hb := h i hi
        rw [remainder_bits hr hp hh,if_pos hia] at hb
        exact hb
      · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) (by omega)))
    · intro i hi
      by_cases hio : i%2=1
      · exact hio
      · have hia := hh i hi
        have hb := h i (by omega)
        rw [remainder_bits hr hp hh,if_neg (by omega)] at hb
        simp [hi] at hb
  · rintro ⟨hl,hu⟩ i hi
    rw [remainder_bits hr hp hh]
    by_cases hia : i<a
    · simp [hia,hl i hi]
    · have hn : i∉post := by intro hm; have h := hu i hm; omega
      simp [hia,hn]

/-- The largest odd-bit-only integer below 2^h has base-four digits 0 or 2.
The parity-sensitive bound is attained by filling every permitted bit. -/
theorem noEven_bound (h : Nat) {r : Nat} (hr : r<2^h) (hn : NoEven r) :
    3*r+2≤2^(h+(if h%2=0 then 1 else 0)) := by
  induction h using Nat.strongRecOn generalizing r with
  | ind h ih =>
    by_cases hh : h<2
    · have hm := hn 0 (by decide)
      rw [Nat.testBit_zero] at hm
      simp only [decide_eq_false_iff_not] at hm
      have he : h=0 ∨ h=1 := by omega
      rcases he with rfl | rfl <;> simp at hr ⊢ <;> omega
    · let q := r/4
      have hpow : 2^h=2^(h-2)*4 := by
        rw [show h=h-2+2 by omega,Nat.pow_add]; rfl
      have hq : q<2^(h-2) := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0<4)).mpr
        omega
      have hqn : NoEven q := by
        intro i hi
        have hb := hn (i+2) (by omega)
        rw [Nat.testBit_add] at hb
        exact hb
      have hlow := hn 0 (by decide)
      rw [Nat.testBit_zero] at hlow
      simp only [decide_eq_false_iff_not] at hlow
      have hrem : r%4≤2 := by omega
      have hb := ih (h-2) (by omega) hq hqn
      have he : (h-2)%2=h%2 := by omega
      rw [he] at hb
      have he' : h+(if h%2=0 then 1 else 0)=(h-2+(if h%2=0 then 1 else 0))+2 := by omega
      rw [he',Nat.pow_add,show 2^2=4 by decide]
      dsimp [q] at hb
      omega

/-- Geometric bound on a sparse sum strictly below its next source. -/
theorem spaced_mass_desc (hs : List Nat) (a : Nat)
    (hp : hs.Pairwise (fun x y => y+4≤x)) (hh : ∀ i∈hs, i+4≤a) :
    15*mass hs<2^a := by
  induction hs generalizing a with
  | nil => simp [Nat.two_pow_pos]
  | cons i is ih =>
    obtain ⟨hi,his⟩ := List.pairwise_cons.mp hp
    have htail := ih i his (by intro j hj; exact hi j hj)
    have hia := hh i (by simp)
    have hpow : 16*2^i≤2^a := by
      have h := Nat.pow_le_pow_right (by decide : 0<2) hia
      rw [Nat.pow_add,show 2^4=16 by decide,Nat.mul_comm] at h
      exact h
    rw [mass_cons]
    omega

theorem spaced_mass (hs : List Nat) (a : Nat) (hp : Spaced hs)
    (hh : ∀ i∈hs, i+4≤a) : 15*mass hs<2^a := by
  have hr : hs.reverse.Pairwise (fun x y => y+4≤x) := by
    rw [List.pairwise_reverse]; exact hp
  have hb := spaced_mass_desc hs.reverse a hr (by intro i hi; exact hh i (by simpa using hi))
  simpa [mass,List.map_reverse,List.sum_reverse] using hb

/-- For a positive signed debt and a spaced queue, every odd-only output
is exactly an odd-only remainder below the crossing source plus odd high
sources.  The crossing source is constrained to within a factor 3 of debt;
when its position is odd the lower bound is twice as strong. -/
theorem gate_exact {hs : List Nat} {d : Nat} (hp : Spaced hs)
    (hd : 0<d) (hm : d≤mass hs) :
    ∃ pre a post r, hs=pre++a::post ∧ mass pre<d ∧ d≤mass pre+2^a ∧
      r=mass pre+2^a-d ∧ r<2^a ∧ mass hs-d=r+mass post ∧
      (NoEven (mass hs-d) ↔ NoEven r ∧ ∀ i∈post, i%2=1) ∧
      15*d<16*2^a ∧
      (NoEven (mass hs-d) →
        (if a%2=0 then 2^a else 2^(a+1))+2≤3*d) := by
  obtain ⟨pre,a,post,he,hl,hu⟩ := crossing_exists hs d hd hm
  obtain ⟨heq,hr⟩ := crossing_remainder (post:=post) hl hu
  let r := mass pre+2^a-d
  have hp' : Spaced (pre++a::post) := he ▸ hp
  obtain ⟨hpre,hpost,hcross⟩ := List.pairwise_append.mp hp'
  obtain ⟨ha,hps⟩ := List.pairwise_cons.mp hpost
  have hps' : post.Pairwise (· < ·) := hps.imp (by intro a b h; omega)
  have hhigh : ∀ i∈post,a≤i := by intro i hi; have h:=ha i hi; omega
  have hgate := noEven_remainder_iff (r:=r) hr hps' hhigh
  have heq' : mass hs-d=r+mass post := he ▸ heq
  have hlow := spaced_mass pre a hpre (by intro i hi; exact hcross i hi a (by simp))
  refine ⟨pre,a,post,r,he,hl,hu,rfl,hr,heq',?_,by omega,?_⟩
  · rw [heq']; exact hgate
  · intro hn
    have hn' : NoEven r := (hgate.mp (heq' ▸ hn)).1
    have hb := noEven_bound a hr hn'
    by_cases h : a%2=0
    · simp [h,Nat.pow_succ] at hb ⊢
      omega
    · simp [h,Nat.pow_succ] at hb ⊢
      omega

#print axioms gate_exact
#print axioms noEven_bound
#print axioms spaced_mass

end BB6.Agent32F418.SparseGate
