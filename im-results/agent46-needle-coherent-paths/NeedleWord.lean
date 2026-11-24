import Std

namespace NeedleWord

def S : List Nat → Nat
  | [] => 0
  | v::w => v+1+S w

def L : List Nat → Nat
  | [] => 1
  | v::w => (2^(v+1)+3)*L w

inductive Path : List Nat → Nat → Nat → Prop where
  | nil (p : Nat) : Path [] p p
  | cons {w : List Nat} {p b c : Nat} (v q : Nat)
      (hp : p=2^v*(2*q+3)) (hb : b=p+v+3*(q+1))
      (rest : Path w b c) : Path (v::w) p c

theorem weight_ge_length (w : List Nat) : w.length≤S w := by
  induction w with
  | nil => decide
  | cons v w ih => simp [S]; omega

theorem product_odd (w : List Nat) : L w % 2=1 := by
  induction w with
  | nil => decide
  | cons v w ih =>
    have hd : (2^(v+1)+3)%2=1 := by simp [Nat.pow_succ,Nat.add_mod]
    simp [L,Nat.mul_mod,hd,ih]

theorem product_coprime (w : List Nat) : (2^S w).Coprime (L w) := by
  have h : (L w).Coprime 2 := by
    unfold Nat.Coprime
    rw [Nat.gcd_comm,Nat.gcd_rec,product_odd]
    decide
  exact Nat.coprime_comm.mp (h.pow_right (S w))

theorem path_transport {w : List Nat} {p c : Nat} (h : Path w p c) (u : Nat) :
    Path w (p+2^S w*u) (c+L w*u) := by
  induction h generalizing u with
  | nil p => simpa [S,L] using Path.nil (p+u)
  | @cons w p b c v q hp hb rest ih =>
    let q' := q+2^S w*u
    let b' := b+2^S w*((2^(v+1)+3)*u)
    have hp' : p+2^S (v::w)*u=2^v*(2*q'+3) := by
      simp [q',S,Nat.pow_add,Nat.pow_succ,hp]
      grind
    have hb' : b'=(p+2^S (v::w)*u)+v+3*(q'+1) := by
      simp [b',q',S,Nat.pow_add,Nat.pow_succ,hb]
      grind
    have ht := ih ((2^(v+1)+3)*u)
    have hc : c+L w*((2^(v+1)+3)*u)=c+L (v::w)*u := by simp [L]; ac_rfl
    rw [hc] at ht
    exact Path.cons v q' hp' hb' ht

theorem edge_delta (v q q' p b p' b' : Nat)
    (hp : p=2^v*(2*q+3)) (hb : b=p+v+3*(q+1))
    (hp' : p'=2^v*(2*q'+3)) (hb' : b'=p'+v+3*(q'+1)) :
    (2:Int)^(v+1)*((b':Int)-(b:Int)) = ((2:Int)^(v+1)+3)*((p':Int)-(p:Int)) := by
  subst p; subst p'; subst b; subst b'
  push_cast
  simp [Int.pow_succ]
  grind

theorem path_delta {w : List Nat} {p c p' c' : Nat} (h : Path w p c) (h' : Path w p' c') :
    (2:Int)^S w*((c':Int)-(c:Int)) = (L w:Int)*((p':Int)-(p:Int)) := by
  induction h generalizing p' c' with
  | nil p => cases h'; simp [S,L]
  | @cons w p b c v q hp hb rest ih =>
    cases h' with
    | @cons _ _ b' _ _ q' hp' hb' rest' =>
      have hd := edge_delta v q q' p b p' b' hp hb hp' hb'
      have ht := ih rest'
      simp only [S,L,Int.pow_add]
      push_cast
      calc
        (2:Int)^(v+1)*2^S w*((c':Int)-(c:Int)) = 2^(v+1)*(2^S w*((c':Int)-(c:Int))) := by ac_rfl
        _ = 2^(v+1)*((L w:Int)*((b':Int)-(b:Int))) := by rw [ht]
        _ = (L w:Int)*(2^(v+1)*((b':Int)-(b:Int))) := by ac_rfl
        _ = (L w:Int)*((2^(v+1)+3)*((p':Int)-(p:Int))) := by rw [hd]
        _ = (2^(v+1)+3)*(L w:Int)*((p':Int)-(p:Int)) := by ac_rfl

theorem cylinder_unique {w : List Nat} {p c p' c' : Nat} (h : Path w p c) (h' : Path w p' c') :
    (2:Int)^S w ∣ (p':Int)-(p:Int) := by
  have hd := path_delta h h'
  have hh : (2:Int)^S w ∣ (L w:Int)*((p':Int)-(p:Int)) := by rw [←hd]; exact Int.dvd_mul_right _ _
  have hn := Int.natAbs_dvd_natAbs.mpr hh
  rw [Int.natAbs_pow,Int.natAbs_mul] at hn
  simp at hn
  change 2^S w ∣ L w * ((p':Int)-(p:Int)).natAbs at hn
  have hn' := (product_coprime w).dvd_of_dvd_mul_left hn
  apply Int.natAbs_dvd_natAbs.mp
  simpa [Int.natAbs_pow] using hn'

theorem path_nondecreasing {w : List Nat} {p c : Nat} (h : Path w p c) : p≤c := by
  induction h with
  | nil => omega
  | cons v q hp hb rest ih => omega

theorem path_increasing {w : List Nat} {p c : Nat} (h : Path w p c) (hw : w≠[]) : p<c := by
  cases h with
  | nil => contradiction
  | cons v q hp hb rest => have hh := path_nondecreasing rest; omega

theorem repetition_delta (w : List Nat) (f : Nat → Nat) (r : Nat)
    (h : ∀ i, i≤r → Path w (f i) (f (i+1))) :
    (2:Int)^(S w*r)*((f (r+1):Int)-(f r:Int)) = (L w:Int)^r*((f 1:Int)-(f 0:Int)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hi := ih (fun i hi => h i (by omega))
    have hd := path_delta (h r (by omega)) (h (r+1) (by omega))
    rw [Nat.mul_succ,Int.pow_add,Int.pow_succ]
    calc
      (2:Int)^(S w*r)*2^S w*((f (r+1+1):Int)-(f (r+1):Int))
          = 2^(S w*r)*(2^S w*((f (r+1+1):Int)-(f (r+1):Int))) := by ac_rfl
      _ = 2^(S w*r)*((L w:Int)*((f (r+1):Int)-(f r:Int))) := by rw [hd]
      _ = (L w:Int)*(2^(S w*r)*((f (r+1):Int)-(f r:Int))) := by ac_rfl
      _ = (L w:Int)*((L w:Int)^r*((f 1:Int)-(f 0:Int))) := by rw [hi]
      _ = (L w:Int)^r*(L w:Int)*((f 1:Int)-(f 0:Int)) := by ac_rfl

theorem repetition_bound (w : List Nat) (hw : w≠[]) (f : Nat → Nat) (r : Nat)
    (h : ∀ i, i≤r → Path w (f i) (f (i+1))) :
    2^(S w*r)≤f 1-f 0 := by
  have hd := repetition_delta w f r h
  have hf := path_increasing (h 0 (by omega)) hw
  change f 0 < f 1 at hf
  have hdiv : (2:Int)^(S w*r) ∣ (L w:Int)^r*((f 1:Int)-(f 0:Int)) := by
    rw [←hd]; exact Int.dvd_mul_right _ _
  have hn := Int.natAbs_dvd_natAbs.mpr hdiv
  rw [Int.natAbs_pow,Int.natAbs_mul,Int.natAbs_pow] at hn
  simp at hn
  change 2^(S w*r) ∣ L w^r*((f 1:Int)-(f 0:Int)).natAbs at hn
  have hc : (2^(S w*r)).Coprime (L w^r) := by
    rw [Nat.pow_mul]
    exact ((product_coprime w).pow_left r).pow_right r
  have hh := hc.dvd_of_dvd_mul_left hn
  have habs : ((f 1:Int)-(f 0:Int)).natAbs=f 1-f 0 := by omega
  rw [habs] at hh
  exact Nat.le_of_dvd (by omega) hh

theorem pow_two_gt (n : Nat) : n<2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    have hp := Nat.two_pow_pos n
    omega

theorem no_infinite_repetition (w : List Nat) (hw : w≠[]) (f : Nat → Nat) :
    ¬ (∀ i, Path w (f i) (f (i+1))) := by
  intro h
  let r := f 1-f 0
  have hs : 0<S w := by cases w with | nil => contradiction | cons v w => simp [S]; omega
  have hh := repetition_bound w hw f r (fun i _ => h i)
  have hr : r≤S w*r := by
    have hmul := Nat.mul_le_mul_right r (show 1≤S w by omega)
    simpa using hmul
  have hb := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hr
  have ht := pow_two_gt r
  omega

#print axioms repetition_bound
#print axioms no_infinite_repetition
#print axioms path_transport
#print axioms path_delta
#print axioms cylinder_unique
end NeedleWord
