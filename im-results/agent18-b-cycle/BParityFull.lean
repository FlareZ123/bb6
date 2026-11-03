module
public import Agent18BReduction

@[expose] public section
namespace BB6.BFullCode
open BReduction

/-- A single F step is exactly equivariant under even translations in d. -/
theorem F_lift (p d k : Nat) :
    F (p,d+2*k) = ((F (p,d)).1,(F (p,d)).2+3*k) := by
  simp only [F]
  have hdiv : (d+2*k)/2 = d/2+k := by omega
  have hmod : (d+2*k)%2 = d%2 := by omega
  rw [hdiv,hmod]
  simp only [Prod.mk.injEq]
  constructor
  · trivial
  · omega

/-- Exact 2^n-to-3^n payload difference for fixed n-step parity words. -/
theorem iterF_lift (n p d k : Nat) :
    iterF n (p,d+2^n*k) =
      ((iterF n (p,d)).1, (iterF n (p,d)).2+3^n*k) := by
  induction n generalizing p d k with
  | zero => simp [iterF]
  | succ n ih =>
    have hpow : 2^(n+1)*k = 2*(2^n*k) := by
      rw [Nat.pow_succ]; ac_rfl
    have hpow3 : 3^(n+1)*k = 3^n*(3*k) := by
      rw [Nat.pow_succ]; ac_rfl
    change iterF n (F (p,d+2^(n+1)*k)) =
      ((iterF n (F (p,d))).1, (iterF n (F (p,d))).2 + 3^(n+1)*k)
    rw [hpow, F_lift]
    have hadd : 3*(2^n*k) = 2^n*(3*k) := by ac_rfl
    rw [hadd,hpow3]
    exact ih (F (p,d)).1 (F (p,d)).2 (3*k)

/-- The first n input payload parity bits, in time order. -/
def bits : Nat → Nat × Nat → List Nat
  | 0, _ => []
  | n+1, s => bits n s ++ [(iterF n s).2 % 2]

/-- All payloads in the same residue class mod 2^n have identical first n bits. -/
theorem bits_shift (n p d k : Nat) :
    bits n (p,d+2^n*k) = bits n (p,d) := by
  induction n generalizing p d k with
  | zero => rfl
  | succ n ih =>
    have hpow : 2^(n+1)*k = 2^n*(2*k) := by
      rw [Nat.pow_succ]; ac_rfl
    rw [hpow]
    simp only [bits]
    have hwords := ih p d (2*k)
    rw [hwords]
    have hf := iterF_lift n p d (2*k)
    rw [hf]
    simp only [Prod.snd]
    congr 1
    have heven : 3^n*(2*k) = 2*(3^n*k) := by ac_rfl
    rw [heven]
    simp [Nat.add_mod, Nat.mul_mod]

theorem three_pow_odd (n : Nat) : 3^n % 2 = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

/-- Appending one parity bit can be achieved by adding 2^n to the seed. -/
theorem bits_flip (n p d : Nat) :
    bits (n+1) (p,d+2^n) =
      bits n (p,d) ++ [1 - ((iterF n (p,d)).2 % 2)] := by
  have hb : bits n (p,d+2^n) = bits n (p,d) := by
    simpa using bits_shift n p d 1
  have hf : iterF n (p,d+2^n) =
      ((iterF n (p,d)).1, (iterF n (p,d)).2+3^n) := by
    simpa using iterF_lift n p d 1
  have ho : 3^n %2 = 1 := three_pow_odd n
  have hmod : ((iterF n (p,d)).2+3^n)%2 =
      1 - ((iterF n (p,d)).2%2) := by omega
  simp only [bits]
  rw [hb,hf]
  simp only [Prod.snd]
  rw [hmod]

/-- The parity list can also be unfolded in chronological order. -/
theorem bits_cons (n : Nat) (s : Nat × Nat) :
    bits (n+1) s = s.2 % 2 :: bits n (F s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    change (bits (n+1) s ++ [(iterF (n+1) s).2%2]) =
      s.2%2 :: bits (n+1) (F s)
    rw [ih s]
    simp only [bits, iterF, List.cons_append]

/-- A preserved parity bitstream forces a 3:2 difference balance. -/
theorem F_balance (s : Nat × Nat) :
    2*(F s).2 + 3*(F s).1 = 3*s.2 + 4+8*s.1 := by
  rcases s with ⟨p,d⟩
  simp only [F, Prod.fst, Prod.snd]
  omega

theorem F_order (s t : Nat × Nat) (hp : s.1=t.1)
    (hq : (F s).1=(F t).1) (hd : s.2≤t.2) :
    (F s).2 ≤ (F t).2 := by
  have h1 := F_balance s
  have h2 := F_balance t
  omega

theorem F_gap (s t : Nat × Nat) (hp : s.1=t.1)
    (hq : (F s).1=(F t).1) (hd : s.2≤t.2) :
    2*((F t).2-(F s).2) = 3*(t.2-s.2) := by
  have h1 := F_balance s
  have h2 := F_balance t
  have ho := F_order s t hp hq hd
  omega

/-- Matching finite parity lists imply exact congruence of initial payloads. -/
theorem bits_divisible (n : Nat) (s t : Nat × Nat)
    (hp : s.1=t.1) (horder:s.2≤t.2)
    (hbits:bits n s=bits n t) : 2^n ∣ t.2-s.2 := by
  induction n generalizing s t with
  | zero => simp
  | succ n ih =>
    have heq : s.2%2=t.2%2 ∧ bits n (F s)=bits n (F t) := by
      simpa only [bits_cons,List.cons.injEq] using hbits
    have hq : (F s).1 = (F t).1 := by
      rcases s with ⟨p,d⟩
      rcases t with ⟨p',e⟩
      simp only [F,Prod.fst] at *
      exact heq.1
    have ho := F_order s t hp hq horder
    obtain ⟨k,hk⟩ := ih (F s) (F t) hq ho heq.2
    have hgap := F_gap s t hp hq horder
    have hval : 3*(t.2-s.2) = 2^(n+1)*k := by
      calc
        3*(t.2-s.2) = 2*((F t).2-(F s).2) := hgap.symm
        _ = 2*(2^n*k) := by rw [hk]
        _ = 2^(n+1)*k := by rw [Nat.pow_succ]; ac_rfl
    have hdiv : 2^(n+1) ∣ 3*(t.2-s.2) := ⟨k,hval⟩
    have hcop : Nat.Coprime (2^(n+1)) 3 :=
      Nat.Coprime.pow_left (n+1) (by decide : Nat.Coprime 2 3)
    exact hcop.dvd_of_dvd_mul_left hdiv

/-- The unique small representative producing a prescribed finite word. -/
theorem bits_injective_small (n p d e : Nat)
    (hd : d<2^n) (he:e<2^n)
    (hw : bits n (p,d)=bits n (p,e)) : d=e := by
  rcases Nat.le_total d e with hle | hle
  · have hh := bits_divisible n (p,d) (p,e) rfl hle hw
    by_cases hde : d=e
    · exact hde
    · have hpositive : 0 < e-d := by omega
      have hlarge : 2^n ≤ e-d := Nat.le_of_dvd hpositive hh
      omega
  · have hh := bits_divisible n (p,e) (p,d) rfl hle hw.symm
    by_cases hde : d=e
    · exact hde
    · have hpositive : 0 < d-e := by omega
      have hlarge : 2^n ≤ d-e := Nat.le_of_dvd hpositive hh
      omega

theorem list_reverse_induction {α : Type} (P : List α → Prop)
    (h0 : P []) (hs : ∀ (w : List α) (b : α), P w → P (w ++ [b])) :
    ∀ w, P w := by
  intro w
  have hrev : ∀ y : List α, P y.reverse := by
    intro y
    induction y with
    | nil => simpa using h0
    | cons b y ih => simpa using hs y.reverse b ih
  simpa using hrev w.reverse

/-- Every finite binary parity itinerary is realized by a canonical natural seed. -/
theorem bits_surjective : ∀ (w : List Nat),
    (∀ b : Nat, b ∈ w → b ≤ 1) → ∀ (p : Nat),
    ∃ d : Nat, d < 2^w.length ∧ bits w.length (p,d) = w := by
  intro w
  induction w using list_reverse_induction with
  | h0 =>
    intro hw p
    exact ⟨0,by decide,rfl⟩
  | hs w b ih =>
    intro hw p
    have hw0 : ∀ x : Nat, x ∈ w → x ≤ 1 := by
      intro x hx
      exact hw x (List.mem_append.mpr (Or.inl hx))
    have hb : b ≤ 1 := hw b (by simp)
    obtain ⟨d, hbound, hbits⟩ := ih hw0 p
    let q := (iterF w.length (p,d)).2%2
    have hq : q ≤ 1 := by dsimp [q]; omega
    have hbound_shift : d+2^w.length < 2^(w.length+1) := by
      rw [Nat.pow_succ]
      omega
    have hbound_self : d < 2^(w.length+1) := by
      rw [Nat.pow_succ]
      omega
    by_cases heq : q = b
    · refine ⟨d, ?_, ?_⟩
      · simpa using hbound_self
      · simp only [List.length_append, List.length_singleton, Nat.add_comm]
        change bits (w.length+1) (p,d) = w ++ [b]
        rw [bits,hbits]
        simp [q,heq]
    · refine ⟨d+2^w.length, ?_, ?_⟩
      · simpa using hbound_shift
      · simp only [List.length_append, List.length_singleton, Nat.add_comm]
        change bits (w.length+1) (p,d+2^w.length) = w ++ [b]
        rw [bits_flip,hbits]
        have : 1-q=b := by omega
        simpa [q] using this

/-- A finite binary word is in exact bijection with one canonical 2-adic residue. -/
theorem bits_unique (w : List Nat)
    (hw : ∀ b : Nat, b ∈ w → b ≤ 1) (p : Nat) :
    ∃ d : Nat, (d < 2^w.length ∧ bits w.length (p,d) = w) ∧
      ∀ e : Nat, (e < 2^w.length ∧ bits w.length (p,e) = w) → e = d := by
  obtain ⟨d,hd,hword⟩ := bits_surjective w hw p
  refine ⟨d, ⟨hd,hword⟩, ?_⟩
  intro e he
  exact bits_injective_small w.length p e d he.1 hd (he.2.trans hword.symm)

#print axioms bits_unique
#print axioms bits_injective_small
#print axioms bits_surjective
#print axioms iterF_lift
#print axioms bits_shift
end BB6.BFullCode
