import Std

namespace BB6.Agent43ChunkProduct

/-- Little-endian fixed-width words. The represented integer is used only in
    statements; certificates can work with the individual bounded words. -/
def join (w : Nat) : List Nat → Nat
  | [] => 0
  | x::xs => x + 2^w * join w xs

def bounded (w : Nat) (xs : List Nat) : Prop := ∀ x ∈ xs, x < 2^w

/-- A streaming product check. Incoming and outgoing carry need not be
    evaluated in terms of the represented giant integer. -/
def MulChain (w m : Nat) : Nat → List Nat → List Nat → Nat → Prop
  | r, [], [], f => r = f
  | r, x::xs, y::ys, f =>
      r + m*x = y + 2^w*((r+m*x)/2^w) ∧
      MulChain w m ((r+m*x)/2^w) xs ys f
  | _, _, _, _ => False

theorem mulChain_eq (w m r f : Nat) (xs ys : List Nat)
    (hc : MulChain w m r xs ys f) :
    r+m*join w xs = join w ys + 2^(w*xs.length)*f := by
  induction xs generalizing ys r with
  | nil =>
    cases ys with
    | nil => simpa [MulChain,join] using hc
    | cons y ys => simp [MulChain] at hc
  | cons x xs ih =>
    cases ys with
    | nil => simp [MulChain] at hc
    | cons y ys =>
      obtain ⟨hstep,htail⟩ := hc
      have htail' := ih ((r+m*x)/2^w) ys htail
      calc
        r+m*join w (x::xs) = (r+m*x)+2^w*(m*join w xs) := by simp only [join,Nat.mul_add]; ac_rfl
        _ = y+2^w*(((r+m*x)/2^w)+m*join w xs) := by have he := congrArg (fun z : Nat => z + 2^w*(m*join w xs)) hstep; rw [Nat.mul_add]; omega
        _ = join w (y::ys)+2^(w*(x::xs).length)*f := by
          rw [htail']; simp only [join,List.length_cons,Nat.mul_succ,Nat.pow_add,Nat.mul_add]; ac_rfl

theorem mulChain_length (w m r f : Nat) (xs ys : List Nat)
    (hc : MulChain w m r xs ys f) : xs.length = ys.length := by
  induction xs generalizing ys r with
  | nil => cases ys <;> simp_all [MulChain]
  | cons x xs ih =>
    cases ys with
    | nil => simp [MulChain] at hc
    | cons y ys => exact congrArg (·+1) (ih _ ys hc.2)

theorem join_bound (w : Nat) (xs : List Nat) (h : bounded w xs) :
    join w xs < 2^(w*xs.length) := by
  induction xs with
  | nil => simp [join]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    have hm := Nat.mul_le_mul_left (2^w) (show join w xs+1≤2^(w*xs.length) by omega)
    simp only [Nat.mul_add,Nat.mul_one] at hm
    simp only [join,List.length_cons,Nat.mul_succ,Nat.pow_add]
    rw [Nat.mul_comm (2^(w*xs.length))]
    omega

theorem mulChain_low (w m f : Nat) (xs ys : List Nat)
    (hc : MulChain w m 0 xs ys f) (hy : bounded w ys) :
    (m*join w xs)%2^(w*xs.length)=join w ys := by
  have he := mulChain_eq w m 0 f xs ys hc
  simp only [Nat.zero_add] at he
  rw [he,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt]
  rw [mulChain_length w m 0 f xs ys hc]
  exact join_bound w ys hy

/-- Doubling computes the OR/AND of each consecutive power-of-two window. -/
def orPow (X : Nat) : Nat → Nat
  | 0 => X
  | k+1 => let z := orPow X k; z ||| (z >>> 2^k)

def andPow (X : Nat) : Nat → Nat
  | 0 => X
  | k+1 => let z := andPow X k; z &&& (z >>> 2^k)

theorem orPow_sound (X k i : Nat) (h : (orPow X k).testBit i=true) :
    ∃ j, j<2^k ∧ X.testBit (i+j)=true := by
  induction k generalizing i with
  | zero => exact ⟨0,by simp,by simpa [orPow] using h⟩
  | succ k ih =>
    simp only [orPow,Nat.testBit_or,Nat.testBit_shiftRight,Bool.or_eq_true] at h
    rcases h with h|h
    · obtain ⟨j,hj,hb⟩ := ih i h
      exact ⟨j,by rw [Nat.pow_succ]; omega,hb⟩
    · obtain ⟨j,hj,hb⟩ := ih (2^k+i) h
      exact ⟨2^k+j,by rw [Nat.pow_succ]; omega,by simpa [show i+(2^k+j)=2^k+i+j by omega] using hb⟩

theorem andPow_sound (X k i : Nat) (h : (andPow X k).testBit i=false) :
    ∃ j, j<2^k ∧ X.testBit (i+j)=false := by
  induction k generalizing i with
  | zero => exact ⟨0,by simp,by simpa [andPow] using h⟩
  | succ k ih =>
    simp only [andPow,Nat.testBit_and,Nat.testBit_shiftRight,Bool.and_eq_false_iff] at h
    rcases h with h|h
    · obtain ⟨j,hj,hb⟩ := ih i h
      exact ⟨j,by rw [Nat.pow_succ]; omega,hb⟩
    · obtain ⟨j,hj,hb⟩ := ih (2^k+i) h
      exact ⟨2^k+j,by rw [Nat.pow_succ]; omega,by simpa [show i+(2^k+j)=2^k+i+j by omega] using hb⟩

/-- One mask certifies all starts 0≤i<limit in a local pair of words. -/
def PairOK (w k limit a b : Nat) : Prop :=
  let X := a+2^w*b
  let mask := 2^limit-1
  orPow X k &&& mask = mask ∧ andPow X k &&& mask = 0

instance (w k limit a b : Nat) : Decidable (PairOK w k limit a b) := by
  unfold PairOK; infer_instance

theorem pairOK_bits (w k limit a b i : Nat) (h : PairOK w k limit a b) (hi : i<limit) :
    (∃ j, j<2^k ∧ (a+2^w*b).testBit (i+j)=true) ∧
    (∃ j, j<2^k ∧ (a+2^w*b).testBit (i+j)=false) := by
  obtain ⟨ho,ha⟩ := h
  have h1 := congrArg (fun x : Nat => x.testBit i) ho
  have h0 := congrArg (fun x : Nat => x.testBit i) ha
  simp [Nat.testBit_two_pow_sub_one,hi] at h1 h0
  exact ⟨orPow_sound _ _ _ h1,andPow_sound _ _ _ h0⟩

/-- At each word, only starts whose entire window is within t valid bits
    are checked. The extra word provides the overlap. -/
def ChunkOK (w k : Nat) : Nat → List Nat → Prop
  | _, [] => True
  | t, a::as => PairOK w k (min w (t+1-2^k)) a (as.headD 0) ∧ ChunkOK w k (t-w) as

/-- Each individual local check stays small, even when the represented
    word would exceed the kernel's large-numeral limit. -/
def check (w k : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | t, a::as => decide (PairOK w k (min w (t+1-2^k)) a (as.headD 0)) && check w k (t-w) as

theorem check_iff (w k t : Nat) (xs : List Nat) : check w k t xs=true ↔ ChunkOK w k t xs := by
  induction xs generalizing t with
  | nil => simp [check,ChunkOK]
  | cons a as ih => simp [check,ChunkOK,ih]

theorem pair_join_bit (w a i : Nat) (as : List Nat)
    (ha : a<2^w) (has : bounded w as) (hi : i<2*w) :
    (a+2^w*as.headD 0).testBit i=(join w (a::as)).testBit i := by
  simp only [join,Nat.add_comm a]
  rw [Nat.testBit_two_pow_mul_add _ ha,Nat.testBit_two_pow_mul_add _ ha]
  split
  · rfl
  · rename_i h
    have hj : i-w<w := by omega
    cases as with
    | nil => simp [join]
    | cons b bs =>
      have hb := has b (by simp)
      simp only [List.headD_cons,join,Nat.add_comm b]
      rw [Nat.testBit_two_pow_mul_add _ hb,if_pos hj]

theorem chunkOK_bits (w k t : Nat) (xs : List Nat)
    (hkw : 2^k≤w) (ht : t≤w*xs.length) (hb : bounded w xs)
    (h : ChunkOK w k t xs) (i : Nat) (hi : i+2^k≤t) :
    (∃ j, j<2^k ∧ (join w xs).testBit (i+j)=true) ∧
    (∃ j, j<2^k ∧ (join w xs).testBit (i+j)=false) := by
  induction xs generalizing t i with
  | nil => simp at ht; have := Nat.two_pow_pos k; omega
  | cons a as ih =>
    have ha := hb a (by simp)
    have has : bounded w as := fun x hx => hb x (by simp [hx])
    obtain ⟨hpair,htail⟩ := h
    by_cases hil : i<w
    · have hilim : i<min w (t+1-2^k) := by omega
      obtain ⟨⟨j1,hj1,h1⟩,⟨j0,hj0,h0⟩⟩ := pairOK_bits w k _ a (as.headD 0) i hpair hilim
      exact ⟨⟨j1,hj1,by rwa [←pair_join_bit w a (i+j1) as ha has (by omega)]⟩,
             ⟨j0,hj0,by rwa [←pair_join_bit w a (i+j0) as ha has (by omega)]⟩⟩
    · have ht' : t-w≤w*as.length := by simp only [List.length_cons,Nat.mul_succ] at ht; omega
      obtain ⟨⟨j1,hj1,h1⟩,⟨j0,hj0,h0⟩⟩ := ih (t-w) ht' has htail (i-w) (by omega)
      have he (j : Nat) : (join w (a::as)).testBit (i+j)=(join w as).testBit (i-w+j) := by
        simp only [join,Nat.add_comm a]
        rw [Nat.testBit_two_pow_mul_add _ ha,if_neg (by omega : ¬i+j<w),show i+j-w=i-w+j by omega]
      exact ⟨⟨j1,hj1,by rwa [he]⟩,⟨j0,hj0,by rwa [he]⟩⟩

/-- Core certificate transfer: verified local multiplication by m, combined
    with verified local overlapping windows, supplies every mixed window
    of the actual product, without evaluating the giant product. -/
theorem product_windows (w k t m f : Nat) (xs ys : List Nat)
    (hkw : 2^k≤w) (ht : t≤w*xs.length) (hy : bounded w ys)
    (hc : MulChain w m 0 xs ys f) (hcheck : ChunkOK w k t ys)
    (i : Nat) (hi : i+2^k≤t) :
    (∃ j, j<2^k ∧ (m*join w xs).testBit (i+j)=true) ∧
    (∃ j, j<2^k ∧ (m*join w xs).testBit (i+j)=false) := by
  have hlen := mulChain_length w m 0 f xs ys hc
  have hlow := mulChain_low w m f xs ys hc hy
  obtain ⟨⟨j1,hj1,h1⟩,⟨j0,hj0,h0⟩⟩ := chunkOK_bits w k t ys hkw (by rwa [←hlen]) hy hcheck i hi
  have he (j : Nat) (hj : j<2^k) : (join w ys).testBit (i+j)=(m*join w xs).testBit (i+j) := by
    rw [←hlow,Nat.testBit_mod_two_pow]
    simp [show i+j<w*xs.length by omega]
  exact ⟨⟨j1,hj1,by rwa [←he j1 hj1]⟩,⟨j0,hj0,by rwa [←he j0 hj0]⟩⟩

/-- Adjacent multiplication batches compose with only their small shared carry. -/
theorem mulChain_append (w m r mid f : Nat) (xs ys us vs : List Nat)
    (h₁ : MulChain w m r xs ys mid) (h₂ : MulChain w m mid us vs f) :
    MulChain w m r (xs++us) (ys++vs) f := by
  induction xs generalizing r ys with
  | nil =>
    cases ys with
    | nil => simp only [MulChain] at h₁; subst r; simpa using h₂
    | cons y ys => simp [MulChain] at h₁
  | cons x xs ih =>
    cases ys with
    | nil => simp [MulChain] at h₁
    | cons y ys => exact ⟨h₁.1,ih _ ys h₁.2⟩

/-- The lookahead word at a batch boundary is explicit. It may be zero only
    at the end of the whole word. -/
def SegmentOK (w k : Nat) : Nat → List Nat → Nat → Prop
  | _, [], _ => True
  | t, a::as, b => PairOK w k (min w (t+1-2^k)) a (as.headD b) ∧
      SegmentOK w k (t-w) as b

theorem segmentOK_append (w k t b : Nat) (xs ys : List Nat)
    (h₁ : SegmentOK w k t xs (ys.headD b))
    (h₂ : SegmentOK w k (t-w*xs.length) ys b) :
    SegmentOK w k t (xs++ys) b := by
  induction xs generalizing t with
  | nil => simpa using h₂
  | cons a as ih =>
    have ht : t-w*(a::as).length = t-w-w*as.length := by
      simp only [List.length_cons,Nat.mul_succ]; omega
    have hhead : (as++ys).headD b=as.headD (ys.headD b) := by cases as <;> rfl
    exact ⟨by change PairOK w k (min w (t+1-2^k)) a ((as++ys).headD b); rw [hhead]; exact h₁.1,ih (t-w) h₁.2 (by rwa [←ht])⟩

theorem segmentOK_zero (w k t : Nat) (xs : List Nat) :
    SegmentOK w k t xs 0 ↔ ChunkOK w k t xs := by
  induction xs generalizing t with
  | nil => simp [SegmentOK,ChunkOK]
  | cons a as ih => simp [SegmentOK,ChunkOK,ih]

#print axioms mulChain_append
#print axioms segmentOK_append
#print axioms segmentOK_zero
#print axioms mulChain_eq
#print axioms mulChain_low
#print axioms chunkOK_bits
#print axioms product_windows
end BB6.Agent43ChunkProduct
