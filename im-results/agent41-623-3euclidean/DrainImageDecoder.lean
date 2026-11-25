import Lean

/-! Exact high-digit inverse of the positive-budget #623 drain image.
All arithmetic is standalone; the source adapter instantiates the recurrence
of Agent49CorrectionGrowth.excess. -/
namespace BB6.Agent41DrainImageDecoder

def tau : Nat → Nat
  | 0 => 0
  | k+1 => 3*tau k+1

theorem tau_pow (k : Nat) : 2*tau k+1=3^k := by
  induction k with
  | zero => decide
  | succ k ih => rw [tau,Nat.pow_succ]; omega

theorem tau_parity (k : Nat) : tau k%2=k%2 := by
  induction k with
  | zero => decide
  | succ k ih => rw [tau]; omega

def weight (d : Nat) : Int := if d=1 then 1 else if d=2 then -1 else 0

def charge : Nat → Nat → Int
  | 0,_ => 0
  | k+1,u => charge k (u/3)+weight (u%3)

def code (k u : Nat) : Int := 3*(u:Int)+charge k u

theorem charge_high (k : Nat) : ∀ u d, u<3^k → d<3 →
    charge (k+1) (d*3^k+u)=charge k u+weight d := by
  induction k with
  | zero =>
    intro u d hu hd
    have he : u=0 := by omega
    subst u
    have hh : d=0 ∨ d=1 ∨ d=2 := by omega
    rcases hh with h|h|h <;> subst d <;> decide
  | succ k ih =>
    intro u d hu hd
    have hp : 3^(k+1)=3^k*3 := Nat.pow_succ ..
    have hq : u/3<3^k := by omega
    have he : d*3^(k+1)+u=(d*3^k)*3+u := by rw [hp,←Nat.mul_assoc]
    have hm : (d*3^(k+1)+u)%3=u%3 := by rw [he]; omega
    have hv : (d*3^(k+1)+u)/3=d*3^k+u/3 := by rw [he]; omega
    rw [charge,hm,hv,ih _ _ hq hd,charge]
    omega

theorem code_high (k u d : Nat) (hu : u<3^k) (hd : d<3) :
    code (k+1) (d*3^k+u)=3*(d*3^k:Nat)+weight d+code k u := by
  unfold code
  rw [charge_high k u d hu hd]
  simp only [Int.natCast_add]
  omega

theorem code_range (k : Nat) : ∀ u, u<3^k →
    0≤code k u ∧ code k u≤3*(3^k:Nat)-3-k := by
  induction k with
  | zero =>
    intro u hu
    have h : u=0 := by omega
    subst u
    decide
  | succ k ih =>
    intro u hu
    let d := u/3^k
    let t := u%3^k
    have hp : 0<3^k := Nat.pow_pos (by decide)
    have ht : t<3^k := Nat.mod_lt _ hp
    have hd : d<3 := by
      dsimp [d]
      apply (Nat.div_lt_iff_lt_mul hp).2
      rw [Nat.mul_comm,←Nat.pow_succ]; exact hu
    have he : u=d*3^k+t := by
      dsimp [d,t]; rw [Nat.mul_comm]; exact (Nat.mod_add_div u (3^k)).symm.trans (Nat.add_comm ..)
    have hh := ih t ht
    rw [he,code_high k t d ht hd,Nat.pow_succ]
    have hd' : d=0 ∨ d=1 ∨ d=2 := by
      have hh := hd
      clear_value d
      omega
    rcases hd' with h|h|h <;> rw [h] <;>
      simp [weight,Int.natCast_mul,Int.natCast_pow] at * <;> omega

def leadingDigit (p : Nat) (x : Int) : Nat :=
  if x < 3*(p:Int)+1 then 0 else if x < 6*(p:Int)-1 then 1 else 2

theorem leadingDigit_correct (k u d : Nat) (hu : u<3^k) (hd : d<3) :
    leadingDigit (3^k) (code (k+1) (d*3^k+u))=d := by
  have hh := code_range k u hu
  have hp : 0<3^k := Nat.pow_pos (by decide)
  rw [code_high k u d hu hd]
  unfold leadingDigit
  have hd' : d=0 ∨ d=1 ∨ d=2 := by omega
  rcases hd' with h|h|h <;> subst d <;>
    simp [weight,Int.natCast_mul,Int.natCast_pow] at * <;>
    split <;> (try split) <;> omega

/-- p is the current highest power of three. Each iteration removes one
high digit using disjoint image intervals and divides p by three. -/
def decodeAux : Nat → Nat → Int → Option Nat
  | 0,_,x => if x=0 then some 0 else none
  | k+1,p,x =>
    let d := leadingDigit p x
    (decodeAux k (p/3) (x-3*(d*p:Nat)-weight d)).map (fun u => d*p+u)

def decode (k : Nat) (x : Int) : Option Nat := decodeAux k (3^k/3) x

theorem decode_complete (k : Nat) : ∀ u, u<3^k → decode k (code k u)=some u := by
  induction k with
  | zero =>
    intro u hu
    have h : u=0 := by omega
    subst u
    decide
  | succ k ih =>
    intro u hu
    let d := u/3^k
    let t := u%3^k
    have hp : 0<3^k := Nat.pow_pos (by decide)
    have ht : t<3^k := Nat.mod_lt _ hp
    have hd : d<3 := by
      dsimp [d]; apply (Nat.div_lt_iff_lt_mul hp).2
      rw [Nat.mul_comm,←Nat.pow_succ]; exact hu
    have he : u=d*3^k+t := by dsimp [d,t]; rw [Nat.mul_comm]; exact (Nat.mod_add_div u (3^k)).symm.trans (Nat.add_comm ..)
    have hpow : 3^(k+1)/3=3^k := by rw [Nat.pow_succ]; omega
    unfold decode
    rw [he,hpow,decodeAux,leadingDigit_correct k t d ht hd,code_high k t d ht hd]
    have hz : 3*(d*3^k:Nat)+weight d+code k t-3*(d*3^k:Nat)-weight d=code k t := by omega
    rw [hz]
    exact congrArg (Option.map (fun u => d*3^k+u)) (ih t ht)

theorem decode_sound (k : Nat) : ∀ x u, decode k x=some u →
    u<3^k ∧ code k u=x := by
  induction k with
  | zero =>
    intro x u h
    unfold decode at h
    simp only [decodeAux] at h
    split at h
    · rename_i hx; simp at h; subst u; subst x; decide
    · contradiction
  | succ k ih =>
    intro x u h
    have hpow : 3^(k+1)/3=3^k := by rw [Nat.pow_succ]; omega
    unfold decode at h
    rw [hpow,decodeAux] at h
    generalize hd0 : leadingDigit (3^k) x=d at h
    have hd : d<3 := by rw [←hd0]; unfold leadingDigit; split <;> (try split) <;> omega
    change (decode k (x-3*(d*3^k:Nat)-weight d)).map (fun t => d*3^k+t)=some u at h
    cases he : decode k (x-3*(d*3^k:Nat)-weight d) with
    | none => rw [he] at h; contradiction
    | some t =>
      rw [he] at h
      injection h with hh
      subst u
      have ht := ih _ _ he
      constructor
      · rw [Nat.pow_succ]
        have hh : d=0 ∨ d=1 ∨ d=2 := by omega
        rcases hh with h|h|h <;> rw [h] <;> simp <;> omega
      · rw [code_high k t d ht.1 hd,ht.2]; omega

/-- The positive-budget residue path, encoded in ordinary ternary:
digit 2-r corresponds to residue r. -/
inductive Word : Nat → Nat → Nat → Nat → Prop
  | zero : Word 0 0 0 0
  | r0 {q k u e : Nat} (hq : 0<q) (h : Word (q-1) k u e) :
      Word (3*q) (k+1) (3*u+2) e
  | r1 {q k u e : Nat} (h : Word q k u e) :
      Word (3*q+1) (k+1) (3*u+1) (e+4)
  | r2 {q k u e : Nat} (h : Word (q+1) k u e) :
      Word (3*q+2) (k+1) (3*u) (e+2)

theorem word_exists (b : Nat) : ∃ k u e, Word b k u e := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    by_cases hb : b=0
    · subst b; exact ⟨0,0,0,Word.zero⟩
    · let q := b/3
      have hr : b%3=0 ∨ b%3=1 ∨ b%3=2 := by omega
      rcases hr with h|h|h
      · have hq : 0<q := by omega
        have he : b=3*q := by omega
        obtain ⟨k,u,e,hw⟩ := ih (q-1) (by omega)
        rw [he]; exact ⟨k+1,3*u+2,e,Word.r0 hq hw⟩
      · have he : b=3*q+1 := by omega
        obtain ⟨k,u,e,hw⟩ := ih q (by omega)
        rw [he]; exact ⟨k+1,3*u+1,e+4,Word.r1 hw⟩
      · have he : b=3*q+2 := by omega
        obtain ⟨k,u,e,hw⟩ := ih (q+1) (by omega)
        rw [he]; exact ⟨k+1,3*u,e+2,Word.r2 hw⟩

theorem word_zero_iff {b k u e : Nat} (h : Word b k u e) : b=0 ↔ k=0 := by
  cases h <;> omega

theorem word_range {b k u e : Nat} (h : Word b k u e) :
    u<3^k ∧ 2*u=b+tau k ∧ (e:Int)=2*k+2*charge k u := by
  induction h with
  | zero => decide
  | @r0 q k u e hq h ih =>
    rw [Nat.pow_succ,tau,charge]
    have hm : (3*u+2)%3=2 := by omega
    have hd : (3*u+2)/3=u := by omega
    rw [hm,hd]
    simp [weight]
    omega
  | @r1 q k u e h ih =>
    rw [Nat.pow_succ,tau,charge]
    have hm : (3*u+1)%3=1 := by omega
    have hd : (3*u+1)/3=u := by omega
    rw [hm,hd]
    simp [weight]
    omega
  | @r2 q k u e h ih =>
    rw [Nat.pow_succ,tau,charge]
    have hm : (3*u)%3=0 := by omega
    have hd : (3*u)/3=u := by omega
    rw [hm,hd]
    simp [weight]
    omega

theorem word_lower {b k u e : Nat} (h : Word b k u e) :
    0<k → 3^(k-1)≤u := by
  induction h with
  | zero => omega
  | @r0 q k u e hq h ih =>
    intro hk
    simp only [Nat.add_sub_cancel]
    by_cases hz : k=0
    · simp [hz]
    · have hh := ih (by omega)
      have hp : 3^k=3^(k-1)*3 := by
        conv => lhs; rw [show k=k-1+1 by omega,Nat.pow_succ]
      omega
  | @r1 q k u e h ih =>
    intro hk
    simp only [Nat.add_sub_cancel]
    by_cases hz : k=0
    · simp [hz]
    · have hh := ih (by omega)
      have hp : 3^k=3^(k-1)*3 := by
        conv => lhs; rw [show k=k-1+1 by omega,Nat.pow_succ]
      omega
  | @r2 q k u e h ih =>
    intro hk
    simp only [Nat.add_sub_cancel]
    have hk' : 0<k := by have hh := word_zero_iff h; omega
    have hh := ih hk'
    have hp : 3^k=3^(k-1)*3 := by
      conv => lhs; rw [show k=k-1+1 by omega,Nat.pow_succ]
    omega

theorem word_image {b k u e : Nat} (h : Word b k u e) :
    ((3*b+e:Nat):Int)=2*code k u-3*(tau k:Int)+2*k := by
  have hh := word_range h
  unfold code
  omega

theorem word_parity {b k u e : Nat} (h : Word b k u e) :
    (3*b+e)%2=k%2 := by
  have hh := word_range h
  have hp := tau_parity k
  omega

/-- Upper envelope for all paths of length k. -/
theorem word_upper {b k u e : Nat} (h : Word b k u e) :
    3*b+e≤9*tau k := by
  have hr := word_range h
  have hc := code_range k u hr.1
  have ht := tau_pow k
  have hi := word_image h
  omega

/-- The immediately preceding same-parity length cannot contain this image. -/
theorem word_prev_gap {b k u e : Nat} (h : Word b k u e) (hk : 2≤k) :
    9*tau (k-2)+6≤3*b+e := by
  have hr := word_range h
  have hl := word_lower h (by omega)
  have ht := tau_pow (k-1)
  have h1 : tau k=3*tau (k-1)+1 := by
    conv => lhs; rw [show k=k-1+1 by omega,tau]
  have h2 : tau (k-1)=3*tau (k-2)+1 := by
    conv => lhs; rw [show k-1=k-2+1 by omega,tau]
  omega

/-- Abstract excess equations match the already certified positive-budget
drain arithmetic. -/
structure ExcessLaws (E : Nat → Nat) : Prop where
  zero : E 0=0
  r0 : ∀ q, 0<q → E (3*q)=E (q-1)
  r1 : ∀ q, E (3*q+1)=E q+4
  r2 : ∀ q, E (3*q+2)=E (q+1)+2

theorem word_excess {E : Nat → Nat} (he : ExcessLaws E)
    {b k u e : Nat} (h : Word b k u e) : E b=e := by
  induction h with
  | zero => exact he.zero
  | r0 hq h ih => rw [he.r0 _ hq,ih]
  | r1 h ih => rw [he.r1,ih]
  | r2 h ih => rw [he.r2,ih]

/-- Recover a path from its ordinary ternary word with a nonzero leading
digit. Every such word is a valid terminating positive-budget residue path. -/
theorem word_complete (k u : Nat) (hu : u<3^k)
    (ht : k=0 ∨ 3^(k-1)≤u) : ∃ b e, Word b k u e := by
  induction k generalizing u with
  | zero =>
    have hz : u=0 := by omega
    subst u
    exact ⟨0,0,Word.zero⟩
  | succ k ih =>
    have ht' : 3^k≤u := by simpa using ht
    have hp : 0<3^k := Nat.pow_pos (by decide)
    have hv : u/3<3^k := by rw [Nat.pow_succ] at hu; omega
    have hl : k=0 ∨ 3^(k-1)≤u/3 := by
      by_cases hk : k=0
      · exact Or.inl hk
      · right
        have he : 3^k=3^(k-1)*3 := by
          conv => lhs; rw [show k=k-1+1 by omega,Nat.pow_succ]
        omega
    obtain ⟨b,e,h⟩ := ih (u/3) hv hl
    have hm : u%3=0 ∨ u%3=1 ∨ u%3=2 := by omega
    rcases hm with hr|hr|hr
    · have hb : 0<b := by
        by_cases hb : b=0
        · have hk := (word_zero_iff h).mp hb
          have h0 := word_range h
          simp [hk] at h0
          simp [hk] at ht'
          omega
        · omega
      have hq : b-1+1=b := by omega
      have he : 3*(u/3)=u := by omega
      refine ⟨3*(b-1)+2,e+2,?_⟩
      rw [←he]
      exact Word.r2 (q:=b-1) (by rw [hq]; exact h)
    · have he : 3*(u/3)+1=u := by omega
      refine ⟨3*b+1,e+4,?_⟩
      rw [←he]
      exact Word.r1 h
    · have he : 3*(u/3)+2=u := by omega
      refine ⟨3*(b+1),e,?_⟩
      rw [←he]
      exact Word.r0 (q:=b+1) (by omega) (by simpa using h)

#print axioms decode_complete
#print axioms decode_sound
#print axioms word_exists
#print axioms word_range
#print axioms word_upper
#print axioms word_prev_gap
#print axioms word_excess
#print axioms word_complete

theorem tau_mono {a b : Nat} (h : a≤b) : tau a≤tau b := by
  have ha := tau_pow a
  have hb := tau_pow b
  have hp := Nat.pow_le_pow_right (by decide : 0<3) h
  omega

theorem tau_ge_two (k : Nat) : 2^k≤tau k+1 := by
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ,tau]; omega

theorem word_depth {b k u e : Nat} (h : Word b k u e) :
    k≤(3*b+e).log2+1 := by
  by_cases hk : k=0
  · omega
  · have hl := word_lower h (by omega)
    have hr := word_range h
    have ht := tau_pow (k-1)
    have h1 : tau k=3*tau (k-1)+1 := by
      conv => lhs; rw [show k=k-1+1 by omega,tau]
    have hb : tau (k-1)+1≤b := by omega
    have hp := tau_ge_two (k-1)
    have hy : 3*b+e≠0 := by omega
    have hh := (Nat.le_log2 hy).mpr (show 2^(k-1)≤3*b+e by omega)
    omega

/-- The length search advances by two, maintaining the exact repunit.
It avoids testing opposite-parity bands and does not recompute powers. -/
def bandSearch : Nat → Nat → Nat → Nat → Option (Nat × Nat)
  | 0,_,_,_ => none
  | f+1,k,t,y => if y≤9*t then some (k,t)
    else bandSearch f (k+2) (9*t+4) y

theorem tau_two (k : Nat) : tau (k+2)=9*tau k+4 := by
  rw [tau,tau]; omega

theorem bandSearch_sound (f s y k t : Nat)
    (h : bandSearch f s (tau s) y=some (k,t)) :
    t=tau k ∧ k%2=s%2 := by
  induction f generalizing s with
  | zero => simp [bandSearch] at h
  | succ f ih =>
    rw [bandSearch] at h
    split at h
    · simp only [Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨rfl,rfl⟩
    · rw [←tau_two] at h
      have hh := ih (s+2) h
      omega

theorem bandSearch_complete {b k u e : Nat} (h : Word b k u e) :
    ∀ f s, s≤k → s%2=k%2 → k<s+2*f →
    bandSearch f s (tau s) (3*b+e)=some (k,tau k) := by
  intro f
  induction f with
  | zero => intro s hs hp hf; omega
  | succ f ih =>
    intro s hs hp hf
    rw [bandSearch]
    by_cases he : s=k
    · subst s
      rw [if_pos (word_upper h)]
    · have hs' : s≤k-2 := by omega
      have hm := tau_mono hs'
      have hg := word_prev_gap h (by omega)
      rw [if_neg (by omega),←tau_two]
      exact ih (s+2) (by omega) (by omega) (by omega)

def band (y : Nat) : Option (Nat × Nat) :=
  bandSearch (y.log2+2) (y%2) (y%2) y

theorem tau_bit (y : Nat) : tau (y%2)=y%2 := by
  have h : y%2=0 ∨ y%2=1 := by omega
  rcases h with h|h <;> rw [h] <;> decide

theorem band_sound (y k t : Nat) (h : band y=some (k,t)) :
    t=tau k ∧ k%2=y%2 := by
  unfold band at h
  rw [←tau_bit y] at h
  -- The first start argument remains y%2; restore it explicitly.
  rw [tau_bit y] at h
  have hh : bandSearch (y.log2+2) (y%2) (tau (y%2)) y=some (k,t) := by
    rw [tau_bit y]; exact h
  have h' := bandSearch_sound _ _ _ _ _ hh
  omega

theorem band_complete {b k u e : Nat} (h : Word b k u e) :
    band (3*b+e)=some (k,tau k) := by
  unfold band
  have hp := word_parity h
  have hd := word_depth h
  have hh := bandSearch_complete h ((3*b+e).log2+2) ((3*b+e)%2)
    (by omega) (by omega) (by omega)
  rw [tau_bit] at hh
  exact hh

/-- Direct inverse of y=3*b+E(b), with an optional result.
A failed high-digit interval or forbidden leading-zero word is rejected. -/
def inverse (y : Nat) : Option Nat := do
  let (k,t) ← band y
  let x : Int := ((y:Int)+3*(t:Int)-2*k)/2
  let u ← decode k x
  if k=0 ∨ 3^(k-1)≤u then some (2*u-t) else none

theorem inverse_complete {E : Nat → Nat} (he : ExcessLaws E) (b : Nat) :
    inverse (3*b+E b)=some b := by
  obtain ⟨k,u,e,h⟩ := word_exists b
  have he' := word_excess he h
  rw [he']
  unfold inverse
  rw [band_complete h]
  change (decode k ((((3*b+e:Nat):Int)+3*(tau k:Int)-2*k)/2)).bind
    (fun u => if k=0 ∨ 3^(k-1)≤u then some (2*u-tau k) else none)=some b
  have hi := word_image h
  have hx : (((3*b+e:Nat):Int)+3*(tau k:Int)-2*k)/2=code k u := by omega
  rw [hx,decode_complete k u (word_range h).1]
  simp only [Option.bind_some]
  have ht : k=0 ∨ 3^(k-1)≤u := by
    by_cases hk : k=0
    · exact Or.inl hk
    · exact Or.inr (word_lower h (by omega))
  rw [if_pos ht]
  have hh := (word_range h).2.1
  have hb : 2*u-tau k=b := by omega
  rw [hb]

theorem inverse_sound {E : Nat → Nat} (he : ExcessLaws E) (y b : Nat)
    (h : inverse y=some b) : 3*b+E b=y := by
  unfold inverse at h
  cases hb : band y with
  | none => rw [hb] at h; contradiction
  | some p =>
    rcases p with ⟨k,t⟩
    rw [hb] at h
    simp only [Option.bind_some] at h
    have hs := band_sound y k t hb
    let x : Int := ((y:Int)+3*(t:Int)-2*k)/2
    change (decode k x).bind (fun u => if k=0 ∨ 3^(k-1)≤u then some (2*u-t) else none)=some b at h
    cases hd : decode k x with
    | none => rw [hd] at h; contradiction
    | some u =>
      rw [hd] at h
      simp only [Option.bind_some] at h
      split at h
      · rename_i ht
        injection h with heq
        have hc := decode_sound k x u hd
        obtain ⟨b',e,hw⟩ := word_complete k u hc.1 ht
        have hr := word_range hw
        have he' := word_excess he hw
        have hi := word_image hw
        have hp := word_parity hw
        have hτ := tau_parity k
        have hbb : b'=b := by omega
        subst b'
        rw [he']
        dsimp [x] at hc
        omega
      · contradiction

theorem inverse_iff {E : Nat → Nat} (he : ExcessLaws E) (y b : Nat) :
    inverse y=some b ↔ 3*b+E b=y := by
  constructor
  · exact inverse_sound he y b
  · intro h; rw [←h]; exact inverse_complete he b

theorem inverse_none_iff {E : Nat → Nat} (he : ExcessLaws E) (y : Nat) :
    inverse y=none ↔ ∀ b, 3*b+E b≠y := by
  constructor
  · intro h b hb
    have hh := (inverse_iff he y b).mpr hb
    rw [h] at hh; contradiction
  · intro h
    cases hi : inverse y with
    | none => rfl
    | some b => exact False.elim (h b (inverse_sound he y b hi))

#print axioms band_complete
#print axioms inverse_complete
#print axioms inverse_sound
#print axioms inverse_iff
#print axioms inverse_none_iff


/-- Strengthen the parity-specific lower gap to its exact endpoint. -/
theorem word_lower_image {b k u e : Nat} (h : Word b k u e) (hk : 0<k) :
    3*tau (k-1)+5+2*k≤3*b+e := by
  have hr := word_range h
  have hl := word_lower h hk
  let n := k-1
  have hkn : k=n+1 := by omega
  have hu : u<3^(n+1) := by rw [←hkn]; exact hr.1
  have hu' : 3^n≤u := hl
  let d := u/3^n
  let t := u%3^n
  have hp : 0<3^n := Nat.pow_pos (by decide)
  have ht : t<3^n := Nat.mod_lt _ hp
  have hd : d<3 := by
    dsimp [d]; apply (Nat.div_lt_iff_lt_mul hp).2
    rw [Nat.mul_comm,←Nat.pow_succ]; exact hu
  have hd0 : 0<d := by
    dsimp [d]; exact Nat.div_pos hu' hp
  have he : u=d*3^n+t := by
    dsimp [d,t]; rw [Nat.mul_comm]; exact (Nat.mod_add_div u (3^n)).symm.trans (Nat.add_comm ..)
  have hc := code_range n t ht
  have hlow : 3*(3^n:Nat)+1≤code k u := by
    rw [hkn,he,code_high n t d ht hd]
    have hh : d=1 ∨ d=2 := by
      clear_value d
      omega
    rcases hh with h|h <;> rw [h] <;>
      simp [weight,Int.natCast_mul,Int.natCast_pow] at * <;> omega
  have hi := word_image h
  have hτ := tau_pow n
  have hτ' : tau k=3*tau n+1 := by rw [hkn,tau]
  change 3*tau n+5+2*k≤3*b+e
  rw [←hτ] at hlow
  omega

theorem word_sharp_gap {b k u e : Nat} (h : Word b k u e) (hk : 2≤k) :
    9*tau (k-2)+2*k+8≤3*b+e := by
  have hl := word_lower_image h (by omega)
  have hτ : tau (k-1)=3*tau (k-2)+1 := by
    conv => lhs; rw [show k-1=k-2+1 by omega,tau]
  omega

theorem excess_step_two {E : Nat → Nat} (he : ExcessLaws E) (b : Nat) :
    E b≤E (b+2)+4 := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    by_cases hb : b=0
    · subst b; rw [he.zero]; omega
    · let q := b/3
      have hr : b%3=0 ∨ b%3=1 ∨ b%3=2 := by omega
      rcases hr with h|h|h
      · have hq : 0<q := by omega
        have hb0 : b=3*q := by omega
        have hb2 : b+2=3*q+2 := by omega
        have hh := ih (q-1) (by omega)
        have hh' : q-1+2=q+1 := by omega
        rw [hh'] at hh
        rw [hb2,hb0,he.r0 _ hq,he.r2]
        omega
      · have hb0 : b=3*q+1 := by omega
        have hb2 : b+2=3*(q+1) := by omega
        rw [hb2,hb0,he.r1,he.r0 _ (by omega)]
        simp
      · have hb0 : b=3*q+2 := by omega
        have hb2 : b+2=3*(q+1)+1 := by omega
        rw [hb2,hb0,he.r2,he.r1]
        omega

def image (E : Nat → Nat) (b : Nat) := 3*b+E b

theorem image_min_gap {E : Nat → Nat} (he : ExcessLaws E) (b : Nat) :
    image E b+2≤image E (b+2) ∧
    (image E (b+2)=image E b+2 ↔ b%3=1) := by
  have hh := excess_step_two he b
  constructor
  · unfold image; omega
  · by_cases hb : b=0
    · subst b
      have e0 := he.zero
      have e1 := he.r1 0
      have e2 := he.r2 0
      simp [image,e0] at e1 e2 ⊢
      omega
    · let q := b/3
      have hr : b%3=0 ∨ b%3=1 ∨ b%3=2 := by omega
      rcases hr with h|h|h
      · have hq : 0<q := by omega
        have hb0 : b=3*q := by omega
        have hb2 : b+2=3*q+2 := by omega
        have hh := excess_step_two he (q-1)
        have hh' : q-1+2=q+1 := by omega
        rw [hh'] at hh
        unfold image
        rw [hb2,hb0,he.r0 _ hq,he.r2]
        simp [h]
        omega
      · have hb0 : b=3*q+1 := by omega
        have hb2 : b+2=3*(q+1) := by omega
        unfold image
        rw [hb2,hb0,he.r1,he.r0 _ (by omega)]
        simp
        omega
      · have hb0 : b=3*q+2 := by omega
        have hb2 : b+2=3*(q+1)+1 := by omega
        unfold image
        rw [hb2,hb0,he.r2,he.r1]
        simp [h]
        omega

theorem image_progression {E : Nat → Nat} (he : ExcessLaws E) (b k : Nat) :
    image E b+2*k≤image E (b+2*k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := (image_min_gap he (b+2*k)).1
    rw [show b+2*(k+1)=b+2*k+2 by omega]
    omega

theorem image_parity {E : Nat → Nat} (he : ExcessLaws E) (b : Nat) :
    image E b%2=b%2 := by
  obtain ⟨k,u,e,h⟩ := word_exists b
  have hh := word_range h
  have hp := word_parity h
  have ht := tau_parity k
  have he' := word_excess he h
  unfold image
  omega

theorem image_adjacent {E : Nat → Nat} (he : ExcessLaws E) (b c : Nat)
    (h : image E c=image E b+2) : c=b+2 := by
  have hb := image_parity he b
  have hc := image_parity he c
  by_cases hbc : b≤c
  · have heq : c=b+2*((c-b)/2) := by omega
    have hh := image_progression he b ((c-b)/2)
    rw [←heq,h] at hh
    by_cases h0 : c=b
    · subst c; omega
    · omega
  · have heq : b=c+2*((b-c)/2) := by omega
    have hh := image_progression he c ((b-c)/2)
    rw [←heq,h] at hh
    omega

/-- No three consecutive outputs of a fixed parity are all in the
positive-budget drain image. This holds across band boundaries as well. -/
theorem no_three_images {E : Nat → Nat} (he : ExcessLaws E) (y b c d : Nat)
    (hb : image E b=y) (hc : image E c=y+2) (hd : image E d=y+4) : False := by
  have hbc : image E c=image E b+2 := by omega
  have hcd : image E d=image E c+2 := by omega
  have h1 := image_adjacent he b c hbc
  have h2 := image_adjacent he c d hcd
  subst c; subst d
  have h3 := (image_min_gap he b).2.mp hbc
  have h4 := (image_min_gap he (b+2)).2.mp hcd
  omega

theorem inverse_no_three {E : Nat → Nat} (he : ExcessLaws E) (y : Nat) :
    inverse y=none ∨ inverse (y+2)=none ∨ inverse (y+4)=none := by
  cases hb : inverse y with
  | none => exact Or.inl rfl
  | some b =>
    cases hc : inverse (y+2) with
    | none => exact Or.inr (Or.inl rfl)
    | some c =>
      cases hd : inverse (y+4) with
      | none => exact Or.inr (Or.inr rfl)
      | some d =>
        exact False.elim (no_three_images he y b c d
          (inverse_sound he y b hb) (inverse_sound he (y+2) c hc)
          (inverse_sound he (y+4) d hd))

/-- Every length-k positive-budget band is followed by 2*k+10 units of
missing same-parity outputs before the next possible band. -/
theorem band_gap {E : Nat → Nat} (he : ExcessLaws E) (k j : Nat)
    (hj : 1≤j) (hj' : j≤k+5) :
    inverse (9*tau k+2*j)=none := by
  cases h : inverse (9*tau k+2*j) with
  | none => rfl
  | some b =>
    have hy := inverse_sound he _ _ h
    obtain ⟨l,u,e,hw⟩ := word_exists b
    have hE := word_excess he hw
    rw [hE] at hy
    have hp := word_parity hw
    have ht := tau_parity k
    have hgt : k<l := by
      by_cases hle : l≤k
      · have hl := tau_mono hle
        have hh := word_upper hw
        omega
      · omega
    have hkl : k+2≤l := by omega
    have hm := tau_mono (show k≤l-2 by omega)
    have hg := word_sharp_gap hw (by omega)
    omega

#print axioms word_lower_image
#print axioms word_sharp_gap
#print axioms image_min_gap
#print axioms inverse_no_three
#print axioms band_gap

end BB6.Agent41DrainImageDecoder
