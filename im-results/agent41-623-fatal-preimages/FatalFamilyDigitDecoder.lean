import FatalFamilyInfinite

namespace BB6.Agent41FatalInverse

def tau : Nat → Nat
  | 0 => 0
  | k+1 => 3*tau k+1

theorem tau_power (k : Nat) : 2*tau k+1=3^k := by
  induction k with
  | zero => decide
  | succ k ih => rw [tau,Nat.pow_succ]; omega

/-- Right balanced weight is the complement of the ordinary weight after
translation by the ternary repunit. The identity holds even for truncated digits. -/
theorem balanced_ordinary_duality (k : Nat) : ∀ t, bw k t + ow k (t+tau k)=2*k := by
  induction k with
  | zero => intro t; simp [bw,ow,balanced,ordinary]
  | succ k ih =>
    intro t
    have hdiv : (t+tau (k+1))/3=(t+1)/3+tau k := by rw [tau]; omega
    have hm : (t+tau (k+1))%3=(t+1)%3 := by rw [tau]; omega
    have h := ih ((t+1)/3)
    have hr : t%3=0 ∨ t%3=1 ∨ t%3=2 := by omega
    rcases hr with hr|hr|hr
    · have hm1 : (t+1)%3=1 := by omega
      simp [bw,ow,balanced,ordinary,hdiv,hm,hm1,hr] at * <;> omega
    · have hm1 : (t+1)%3=2 := by omega
      simp [bw,ow,balanced,ordinary,hdiv,hm,hm1,hr] at * <;> omega
    · have hm1 : (t+1)%3=0 := by omega
      simp [bw,ow,balanced,ordinary,hdiv,hm,hm1,hr] at * <;> omega

theorem rightIndex_dual (k t : Nat) :
    rightIndex k t = leftIndex k (t+tau k)-3*(tau k:Int)+2*k+2 := by
  have h := balanced_ordinary_duality k t
  unfold rightIndex leftIndex
  omega

def digitWeight (d : Nat) : Nat := if d=1 then 2 else if d=2 then 1 else 0

theorem ow_low (k t : Nat) : ow (k+1) t=ow k (t/3)+digitWeight (t%3) := by
  unfold ow digitWeight
  rw [ordinary]
  have h : t%3=0 ∨ t%3=1 ∨ t%3=2 := by omega
  rcases h with h|h|h <;> simp [h] <;> omega

/-- A high ordinary digit can be removed without computing any lower digit
statistics. -/
theorem ow_high (k : Nat) : ∀ t d, t<3^k → d<3 →
    ow (k+1) (d*3^k+t)=ow k t+digitWeight d := by
  induction k with
  | zero =>
    intro t d ht hd
    have hz : t=0 := by omega
    subst t
    have hh : d=0 ∨ d=1 ∨ d=2 := by omega
    rcases hh with h|h|h <;> subst d <;> decide
  | succ k ih =>
    intro t d ht hd
    have hp : 3^(k+1)=3^k*3 := Nat.pow_succ ..
    have hq : t/3<3^k := by omega
    have he : d*3^(k+1)+t=(d*3^k)*3+t := by rw [hp,←Nat.mul_assoc]
    have hm : (d*3^(k+1)+t)%3=t%3 := by rw [he]; omega
    have hdiv : (d*3^(k+1)+t)/3=d*3^k+t/3 := by rw [he]; omega
    have hh := ih (t/3) d hq hd
    rw [ow_low (k+1),hm,hdiv,hh,ow_low k]
    omega

theorem leftIndex_high (k t d : Nat) (ht : t<3^k) (hd : d<3) :
    leftIndex (k+1) (d*3^k+t)=3*(d*3^k:Nat)+leftIndex k t-digitWeight d := by
  have h := ow_high k t d ht hd
  unfold leftIndex
  rw [h]
  omega

def leadingDigit (k : Nat) (x : Int) : Nat :=
  if x<3*(3^k:Nat)-3 then 0 else if x<6*(3^k:Nat)-2 then 1 else 2

def decode : Nat → Int → Option Nat
  | 0,x => if x = -1 then some 0 else none
  | k+1,x =>
    let d := leadingDigit k x
    (decode k (x-3*(d*3^k:Nat)+digitWeight d)).map (fun r => d*3^k+r)

theorem index_lower (k : Nat) : ∀ t, -1≤leftIndex k t := by
  intro t
  induction t with
  | zero =>
    have hh : ow k 0=0 := by induction k with | zero => rfl | succ k ih => simpa [ow,ordinary] using ih
    simp [leftIndex,hh]
  | succ t ih => have h := leftIndex_step k t; omega

theorem index_upper (k t : Nat) (ht : t<3^k) : leftIndex k t≤3*(3^k:Nat)-4 := by
  unfold leftIndex
  omega

theorem leadingDigit_correct (k t d : Nat) (ht : t<3^k) (hd : d<3) :
    leadingDigit k (leftIndex (k+1) (d*3^k+t))=d := by
  have he := leftIndex_high k t d ht hd
  have hlo := index_lower k t
  have hhi := index_upper k t ht
  have hp : 0<3^k := Nat.pow_pos (by decide)
  have hh : d=0 ∨ d=1 ∨ d=2 := by omega
  rw [he]
  unfold leadingDigit
  rcases hh with h|h|h <;> subst d <;>
    simp [digitWeight,Int.natCast_mul,Int.natCast_pow] <;>
    simp [Int.natCast_pow] at hhi hp <;>
    split <;> (try split) <;> omega

/-- The decoder is complete on the k-digit range. -/
theorem decode_complete (k : Nat) : ∀ t, t<3^k → decode k (leftIndex k t)=some t := by
  induction k with
  | zero =>
    intro t ht
    have h : t=0 := by omega
    subst t
    decide
  | succ k ih =>
    intro t ht
    let d := t/3^k
    let r := t%3^k
    have hp : 0<3^k := Nat.pow_pos (by decide)
    have hr : r<3^k := Nat.mod_lt _ hp
    have hd : d<3 := by dsimp [d]; apply (Nat.div_lt_iff_lt_mul hp).2; rw [Nat.mul_comm,←Nat.pow_succ]; exact ht
    have he : t=d*3^k+r := by dsimp [d,r]; rw [Nat.mul_comm]; exact (Nat.mod_add_div t (3^k)).symm.trans (Nat.add_comm ..)
    rw [he,decode,leadingDigit_correct k r d hr hd,leftIndex_high k r d hr hd]
    have h : 3*(d*3^k:Nat)+leftIndex k r-digitWeight d-3*(d*3^k:Nat)+digitWeight d=leftIndex k r := by omega
    rw [h,ih r hr]; rfl

/-- Every returned candidate is within the range and is an exact preimage. -/
theorem decode_sound (k : Nat) : ∀ x t, decode k x=some t → t<3^k ∧ leftIndex k t=x := by
  induction k with
  | zero =>
    intro x t h
    simp only [decode] at h
    split at h
    · rename_i hx; simp at h; subst t; subst x; decide
    · contradiction
  | succ k ih =>
    intro x t h
    rw [decode] at h
    generalize hd0 : leadingDigit k x = d at h
    have hd : d<3 := by rw [←hd0]; unfold leadingDigit; split <;> (try split) <;> omega
    change (decode k (x-3*(d*3^k:Nat)+digitWeight d)).map (fun r => d*3^k+r)=some t at h
    cases he : decode k (x-3*(d*3^k:Nat)+digitWeight d) with
    | none => rw [he] at h; contradiction
    | some r =>
      rw [he] at h
      injection h with h
      subst t
      have hr := ih _ _ he
      constructor
      · rw [Nat.pow_succ]
        have hp : d=0 ∨ d=1 ∨ d=2 := by omega
        rcases hp with h|h|h <;> rw [h] <;> simp <;> omega
      · rw [leftIndex_high k r d hr.1 hd,hr.2]; omega

/-- Leading zero padding preserves ordinary digits. -/
theorem ordinary_pad (m : Nat) : ∀ l t, t<3^m → ordinary (m+l) t=ordinary m t := by
  induction m with
  | zero =>
    intro l t ht
    have hz : t=0 := by omega
    subst t
    induction l with
    | zero => rfl
    | succ l ih => simp only [Nat.zero_add] at ih ⊢; rw [ordinary.eq_2]; simp only [Nat.zero_div,ih]; decide
  | succ m ih =>
    intro l t ht
    have hp : 3^(m+1)=3^m*3 := Nat.pow_succ ..
    have hq : t/3<3^m := by omega
    rw [show m+1+l=m+l+1 by omega,ordinary]
    rw [ih l (t/3) hq]
    rw [ordinary]

/-- Leading zero padding preserves balanced digits in their signed range. -/
theorem balanced_pad (m : Nat) : ∀ l t, 2*t<3^m → balanced (m+l) t=balanced m t := by
  induction m with
  | zero =>
    intro l t ht
    have hz : t=0 := by omega
    subst t
    induction l with
    | zero => rfl
    | succ l ih => simp only [Nat.zero_add] at ih ⊢; rw [balanced.eq_2]; simp only [show (0+1)/3=0 by decide,ih]; decide
  | succ m ih =>
    intro l t ht
    have hp : 3^(m+1)=3^m*3 := Nat.pow_succ ..
    have ho := pow_three_odd m
    have hq : 2*((t+1)/3)<3^m := by omega
    rw [show m+1+l=m+l+1 by omega,balanced]
    rw [ih l ((t+1)/3) hq]
    rw [balanced]

def decodeRight (m : Nat) (x : Int) : Option Nat :=
  (decode m (x+3*(tau m:Int)-2*m-2)).bind fun u =>
    if tau m≤u then some (u-tau m) else none

theorem decodeRight_complete (m t : Nat) (ht : 2*t<3^m) :
    decodeRight m (rightIndex m t)=some t := by
  have h := rightIndex_dual m t
  have hτ := tau_power m
  have hu : t+tau m<3^m := by omega
  unfold decodeRight
  rw [show rightIndex m t+3*(tau m:Int)-2*m-2=leftIndex m (t+tau m) by omega]
  rw [decode_complete m _ hu]
  simp

theorem decodeRight_sound (m : Nat) (x : Int) (t : Nat) (h : decodeRight m x=some t) :
    2*t<3^m ∧ rightIndex m t=x := by
  unfold decodeRight at h
  cases he : decode m (x+3*(tau m:Int)-2*m-2) with
  | none => rw [he] at h; contradiction
  | some u =>
    rw [he] at h
    simp only [Option.bind_some] at h
    split at h
    · rename_i hu
      injection h with ht
      have hτ := tau_power m
      have h1 := decode_sound m _ _ he
      have h2 := rightIndex_dual m t
      have h3 : t+tau m=u := by omega
      rw [h3,h1.2] at h2
      omega
    · contradiction

/-- Simultaneously translate the full gate to a small digit length and use a
single decoder. The caller supplies the already certified inverse bounds. -/
theorem left_gate_decode (m l p t : Nat) (ht : t<3^m) :
    (p:Int)=leftIndex (m+l) t ↔ decode m p=some t := by
  have h := ordinary_pad m l t ht
  have he : leftIndex (m+l) t=leftIndex m t := by unfold leftIndex ow; rw [h]
  rw [he]
  constructor
  · intro hp; rw [hp]; exact decode_complete m t ht
  · intro hp; exact (decode_sound m _ _ hp).2.symm

theorem right_gate_decode (m l p t : Nat) (ht : 2*t<3^m) :
    (3*(p:Int))=rightIndex (m+l) t ↔ decodeRight m (3*p:Nat)=some t := by
  have h := balanced_pad m l t ht
  have he : rightIndex (m+l) t=rightIndex m t := by unfold rightIndex bw; rw [h]
  rw [he]
  constructor
  · intro hp
    rw [show ((3*p:Nat):Int)=3*(p:Int) by omega,hp]
    exact decodeRight_complete m t ht
  · intro hp
    have hh := (decodeRight_sound m _ _ hp).2
    omega

#print axioms balanced_ordinary_duality
#print axioms rightIndex_dual
#print axioms decode_complete
#print axioms decode_sound
#print axioms ordinary_pad
#print axioms balanced_pad
#print axioms decodeRight_complete
#print axioms decodeRight_sound
#print axioms left_gate_decode
#print axioms right_gate_decode
end BB6.Agent41FatalInverse
