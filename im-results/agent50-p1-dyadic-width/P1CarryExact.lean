import Lean

namespace BB6.P1CarryExact

def total (n : Nat) : Nat := 7 * 2^n

/-- A legal source gap in the shifted coordinates v=(d-1)/2,
    w=(b+12)/2. All actual source guards are retained. -/
inductive LegalGap (n : Nat) : Nat → Nat → Nat → Prop
  | root : LegalGap n 0 1 (total n - n - 2)
  | edge (m v w e v' w' : Nat)
      (h : LegalGap n m v w)
      (he : 0 < e)
      (hstart : 10 ≤ w ∧ w % 2 = 0)
      (hend : 2 ≤ v' ∧ 6 ≤ w')
      (hMass : v' + w' + n + (m+e) + 1 = total n)
      (hrec : v + total n = 2^e * v' + (n+m+3)) :
      LegalGap n (m+e) v' w'

/-- A bit at position m either begins a source edge (one), or
    extends the preceding edge by one dyadic division (zero).
    Zero is forbidden at the initial position. -/
inductive Micro (n : Nat) : Nat → Nat → Nat → Prop
  | root : Micro n 0 1 (total n - n - 2)
  | one (m v w v' w' : Nat) (h : Micro n m v w)
      (hv : v + total n = 2*v' + (n+m+3)) (hw : w = 2*w') :
      Micro n (m+1) v' w'
  | zero (m v w v' w' : Nat) (h : Micro n m v w)
      (hm : 0 < m)
      (hv : v = 2*v') (hw : w + total n = 2*w' + (n+m+3)) :
      Micro n (m+1) v' w'

theorem pow2_ge_1100_mul (n : Nat) (hn : 14 ≤ n) : 1100*n ≤ 2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hbase : n = 13
    · subst n; decide
    · have hp := ih (by omega)
      rw [Nat.pow_succ]
      omega

theorem total_large (n : Nat) (hn : 14 ≤ n) : n+2 ≤ total n := by
  have h := pow2_ge_1100_mul n hn
  simp [total]
  omega

theorem micro_mass (n m v w : Nat) (hn : 14 ≤ n) (h : Micro n m v w) :
    v+w+n+m+1 = total n := by
  induction h with
  | root =>
    have h := total_large n hn
    omega
  | one m v w v' w' h hv hw ih => omega
  | zero m v w v' w' h hm hv hw ih => omega

/-- Both coordinates stay at least the original large left coordinate divided
    by 2^m, once the compulsory leading one has occurred. -/
theorem micro_scaled_lower (n m v w : Nat) (hn : 14 ≤ n)
    (h : Micro n m v w) (hm : m ≤ n) :
    (0 < m → total n - n - 2 ≤ 2^m * v) ∧
    total n - n - 2 ≤ 2^m * w := by
  induction h with
  | root => simp
  | one m v w v' w' h hv hw ih =>
    have hprev := ih (by omega)
    have hlarge := pow2_ge_1100_mul n hn
    have hT : n+m+3 ≤ total n := by simp [total]; omega
    have hV : v ≤ 2*v' := by omega
    rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_assoc]
    constructor
    · intro _
      by_cases hm0 : m=0
      · subst m
        cases h with
        | root =>
          simp
          omega
      · exact Nat.le_trans (hprev.1 (by omega)) (Nat.mul_le_mul_left _ hV)
    · rw [← hw]
      exact hprev.2
  | zero m v w v' w' h hm0 hv hw ih =>
    have hprev := ih (by omega)
    have hlarge := pow2_ge_1100_mul n hn
    have hT : n+m+3 ≤ total n := by simp [total]; omega
    have hW : w ≤ 2*w' := by omega
    rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_assoc]
    constructor
    · intro _
      rw [← hv]
      exact hprev.1 hm0
    · exact Nat.le_trans hprev.2 (Nat.mul_le_mul_left _ hW)

theorem micro_bounds (n m v w : Nat) (hn : 14 ≤ n)
    (h : Micro n m v w) (hm : m ≤ n) :
    (0 < m → 7 ≤ v) ∧ 7 ≤ w ∧ (m < n → 14 ≤ w) := by
  have hp := pow2_ge_1100_mul n hn
  have hlow := micro_scaled_lower n m v w hn h hm
  have hP : 2^m ≤ 2^n := Nat.pow_le_pow_right (by decide) hm
  have hS : 6*2^n < total n - n - 2 := by simp [total]; omega
  constructor
  · intro hmpos
    by_cases hv : 7 ≤ v
    · exact hv
    · have hmul : 2^m*v ≤ 2^n*6 := Nat.mul_le_mul hP (by omega)
      have := hlow.1 hmpos
      omega
  · constructor
    · by_cases hw : 7 ≤ w
      · exact hw
      · have hmul : 2^m*w ≤ 2^n*6 := Nat.mul_le_mul hP (by omega)
        have := hlow.2
        omega
    · intro hmn
      by_cases hw : 14 ≤ w
      · exact hw
      · have hPm : 2^m ≤ 2^(n-1) := Nat.pow_le_pow_right (by decide) (by omega)
        have hmul : 2^m*w ≤ 2^(n-1)*13 := Nat.mul_le_mul hPm (by omega)
        have hpow : 2^n = 2^(n-1)*2 := by
          rw [← Nat.pow_succ]
          congr 1
          omega
        simp [total] at hlow
        omega

/-- Every valid micro trace of length at most n is a genuine legal gap
    trace in the exact source arithmetic, including its terminal state. -/
theorem micro_to_legal (n m v w : Nat) (hn : 14 ≤ n)
    (h : Micro n m v w) (hm : m ≤ n) : LegalGap n m v w := by
  induction h with
  | root => exact LegalGap.root
  | one m v w v' w' h hv hw ih =>
    have hp := micro_bounds n m v w hn h (by omega)
    have hnew := micro_bounds n (m+1) v' w' hn
      (Micro.one m v w v' w' h hv hw) hm
    have hmass := micro_mass n (m+1) v' w' hn
      (Micro.one m v w v' w' h hv hw)
    apply LegalGap.edge m v w 1 v' w' (ih (by omega)) (by omega)
    · have := hp.2.2 (by omega)
      omega
    · have := hnew.1 (by omega)
      omega
    · exact hmass
    · simpa using hv
  | zero m v w v' w' h hm0 hv hw ih =>
    have hp := ih (by omega)
    have hnew := micro_bounds n (m+1) v' w' hn
      (Micro.zero m v w v' w' h hm0 hv hw) hm
    have hmass := micro_mass n (m+1) v' w' hn
      (Micro.zero m v w v' w' h hm0 hv hw)
    cases hp with
    | root => omega
    | edge s u z e v w hpre he hs he' hM hR =>
      have hrec : u+total n = 2^(e+1)*v' + (n+s+3) := by
        rw [Nat.pow_succ, Nat.mul_assoc, ← hv]
        exact hR
      have hmass' : v'+w'+n+(s+(e+1))+1 = total n := by omega
      have hout : LegalGap n (s+(e+1)) v' w' :=
        LegalGap.edge s u z (e+1) v' w' hpre (by omega) hs
          (by have := hnew.1 (by omega); omega) hmass' hrec
      simpa [Nat.add_assoc] using hout


/-- The cost carry is conjugate to the exact shifted-right coordinate for
    every position below n.  Their sum is a multiple of 2^(n-m). -/
theorem carry_step_lift (n m v w c c' : Nat) (bit : Bool)
    (hn : 14 ≤ n) (hm : m < n) (hm0 : 0 < m)
    (h : Micro n m v w)
    (hdvd : 2^(n-m) ∣ v+c)
    (hc : c + (if bit then n+m+3 else 0) = 2*c') :
    ∃ v' w', Micro n (m+1) v' w' ∧ 2^(n-(m+1)) ∣ v'+c' := by
  have hmass := micro_mass n m v w hn h
  have hp := pow2_ge_1100_mul n hn
  have hT : n+m+3 ≤ total n := by simp [total]; omega
  have hsplit : n-m = (n-(m+1))+1 := by omega
  have hpow : 2^(n-m) = 2^(n-(m+1))*2 := by rw [hsplit, Nat.pow_succ]
  obtain ⟨a, ha⟩ := hdvd
  rw [hpow] at ha
  have hTa : total n = (2^(n-(m+1))*2)*(7*2^m) := by
    have heq : n = (n-m)+m := by omega
    calc
      total n = 7*(2^(n-m)*2^m) := by rw [← Nat.pow_add, ← heq]; rfl
      _ = (2^(n-(m+1))*2)*(7*2^m) := by rw [hpow]; ac_rfl
  have hEvenT : total n % 2 = 0 := by
    rw [hTa]
    have hh : (2^(n-(m+1))*2)*(7*2^m) = 2*(2^(n-(m+1))*(7*2^m)) := by ac_rfl
    rw [hh]; simp
  have hEvenVC : (v+c) % 2 = 0 := by
    rw [ha]
    have hh : (2^(n-(m+1))*2)*a = 2*(2^(n-(m+1))*a) := by ac_rfl
    rw [hh]; simp
  cases bit with
  | false =>
    simp at hc
    have hve : v%2=0 := by omega
    have hwe : (w+total n-(n+m+3))%2=0 := by omega
    let v' := v/2
    let w' := (w+total n-(n+m+3))/2
    have hv : v=2*v' := by dsimp [v']; omega
    have hw : w+total n=2*w'+(n+m+3) := by dsimp [w']; omega
    refine ⟨v', w', Micro.zero m v w v' w' h hm0 hv hw, a, ?_⟩
    have hh : v+c = 2*(2^(n-(m+1))*a) := by rw [ha]; ac_rfl
    omega
  | true =>
    simp at hc
    have hwe : w%2=0 := by omega
    have hve : (v+total n-(n+m+3))%2=0 := by omega
    let v' := (v+total n-(n+m+3))/2
    let w' := w/2
    have hv : v+total n=2*v'+(n+m+3) := by dsimp [v']; omega
    have hw : w=2*w' := by dsimp [w']; omega
    refine ⟨v', w', Micro.one m v w v' w' h hv hw, a+7*2^m, ?_⟩
    have hsum : (v+c)+total n = 2*(2^(n-(m+1))*(a+7*2^m)) := by
      rw [ha, hTa]
      calc
        _ = (2^(n-(m+1))*2)*(a+7*2^m) := by rw [Nat.mul_add]
        _ = _ := by ac_rfl
    omega

/-- The compulsory first selected bit gives an exact microstate. -/
theorem carry_first_lift (n : Nat) (hn : 14 ≤ n) (heven : n%2=0) :
    ∃ v w, Micro n 1 v w ∧ 2^(n-1) ∣ v+(n+2)/2 := by
  have hlarge := total_large n hn
  have hpow : 2^n = 2^(n-1)*2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  have hT : total n = 2*(7*2^(n-1)) := by
    simp only [total,hpow]
    ac_rfl
  let a := (total n-n-2)/2
  have hw : total n-n-2 = 2*a := by dsimp [a]; omega
  have hv : 1+total n = 2*a+(n+0+3) := by omega
  refine ⟨a,a, Micro.one 0 1 (total n-n-2) a a Micro.root hv hw, 7, ?_⟩
  have ha : a+(n+2)/2 = 7*2^(n-1) := by omega
  rw [ha]
  ac_rfl


/-- Little-endian weighted Boolean sum, with index j on its first bit.
    Identical to BB6WallCarry.sumBits. -/
def weightedTail (n j : Nat) : List Bool → Nat
  | [] => 0
  | b::bs => (if b then n+3+j else 0)+2*weightedTail n (j+1) bs

theorem carry_tail_lift (n : Nat) (hn : 14 ≤ n) :
    ∀ (xs : List Bool) (m v w c q : Nat),
      0 < m → m+xs.length ≤ n →
      Micro n m v w → 2^(n-m) ∣ v+c →
      c+weightedTail n m xs = 2^xs.length*q →
      ∃ v' w', Micro n (m+xs.length) v' w' ∧
        2^(n-(m+xs.length)) ∣ v'+q := by
  intro xs
  induction xs with
  | nil =>
    intro m v w c q hm0 hmn h hdvd heq
    simp [weightedTail] at heq
    subst q
    exact ⟨v,w,by simpa using h,by simpa using hdvd⟩
  | cons b bs ih =>
    intro m v w c q hm0 hmn h hdvd heq
    let a := if b then n+3+m else 0
    have hEq : c+a+2*weightedTail n (m+1) bs =
        2*(2^bs.length*q) := by
      simp only [weightedTail, List.length_cons, Nat.pow_succ] at heq
      calc
        _ = c+(a+2*weightedTail n (m+1) bs) := by omega
        _ = (2^bs.length*2)*q := heq
        _ = _ := by ac_rfl
    have hc : c+a = 2*((c+a)/2) := by omega
    have ht : (c+a)/2+weightedTail n (m+1) bs=2^bs.length*q := by omega
    have hmn' : m+1+bs.length ≤ n := by simp at hmn; omega
    obtain ⟨v',w',hMicro,hDiv⟩ := carry_step_lift n m v w c ((c+a)/2) b hn
      (by omega) hm0 h hdvd (by simpa [a,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hc)
    obtain ⟨v'',w'',hM,hD⟩ := ih (m+1) v' w' ((c+a)/2) q
      (by omega) hmn' hMicro hDiv ht
    refine ⟨v'',w'',?_,?_⟩
    · simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hM
    · simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hD

/-- Exact converse: any valid weighted bit prefix of positive length K≤n
    gives a legal source-coordinate inverse history of cost EXACTLY K.
    This is not merely a necessary-condition overapproximation. -/
theorem prefix_to_legal (n : Nat) (rest : List Bool)
    (hn : 14 ≤ n) (hK : rest.length+1 ≤ n)
    (hmod : ((n+3)+2*weightedTail n 1 rest)%2^(rest.length+1)=1) :
    ∃ v w, LegalGap n (rest.length+1) v w := by
  let E := (n+3)+2*weightedTail n 1 rest
  let q := E/2^(rest.length+1)
  have hsum : E = 1+2^(rest.length+1)*q := by
    have h := Nat.mod_add_div E (2^(rest.length+1))
    change E%2^(rest.length+1)=1 at hmod
    rw [hmod] at h
    exact h.symm
  rw [Nat.pow_succ] at hsum
  have hsum' : (n+3)+2*weightedTail n 1 rest = 1+2*(2^rest.length*q) := by
    calc
      _ = E := rfl
      _ = 1+(2^rest.length*2)*q := hsum
      _ = _ := by congr 1; ac_rfl
  have heven : n%2=0 := by omega
  have hc : (n+2)/2+weightedTail n 1 rest=2^rest.length*q := by omega
  obtain ⟨v,w,hM,hD⟩ := carry_first_lift n hn heven
  obtain ⟨v',w',hM',_⟩ := carry_tail_lift n hn rest 1 v w ((n+2)/2) q
    (by omega) (by omega) hM hD hc
  refine ⟨v',w',?_⟩
  have hlegal := micro_to_legal n (1+rest.length) v' w' hn hM' (by omega)
  simpa [Nat.add_comm] using hlegal

#print axioms prefix_to_legal
#print axioms carry_first_lift
#print axioms carry_step_lift
#print axioms micro_to_legal
#print axioms micro_bounds
end BB6.P1CarryExact
