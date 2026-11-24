import RenewalGrid

namespace BB6.Agent9Renewal
set_option maxHeartbeats 1000000

/-- Elementary square domination, used only to supply explicit finite
thresholds; no asymptotic library is needed. -/
theorem sq_le_pow2 (t : Nat) (ht : 4≤t) : t*t≤2^t := by
  have h : ∀ j : Nat, (4+j)*(4+j)≤2^(4+j) := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
      let a := 4+j
      have ha : 4≤a := by dsimp [a]; omega
      have hmul := Nat.mul_le_mul_right a (show 3≤a by omega)
      have hsq : (a+1)*(a+1)≤2*(a*a) := by
        have he : (a+1)*(a+1)=a*a+2*a+1 := by grind only
        rw [he]
        omega
      change a*a≤2^a at ih
      have hm := Nat.mul_le_mul_left 2 ih
      have he : 4+(j+1)=a+1 := by dsimp [a]; omega
      rw [he,Nat.pow_succ]
      omega
  have hh := h (t-4)
  rw [show 4+(t-4)=t by omega] at hh
  exact hh

/-- Explicit exponential-versus-polynomial margin. Threshold intentionally
coarse but computable from the two exponents alone. -/
def expThreshold (e d : Nat) : Nat := 2^(4+2*(e+d+1))

theorem exp_dom (e d n : Nat) (hn : expThreshold e d≤n) : 2^e*n^d<2^n := by
  let t := n.log2
  have hnpos : 0<n := by have hh := Nat.two_pow_pos (4+2*(e+d+1)); unfold expThreshold at hn; omega
  have ht : 4+2*(e+d+1)≤t := by
    by_cases hh : 4+2*(e+d+1)≤t
    · exact hh
    · have hlt : t<4+2*(e+d+1) := by omega
      have hp := (Nat.log2_lt (by omega : n≠0)).mp hlt
      unfold expThreshold at hn
      omega
  have htn : 2^t≤n := by
    obtain ⟨h1,h2⟩ := log_window n hnpos
    change 2^(t+1)≤2*n at h2
    rw [Nat.pow_succ] at h2
    omega
  have hs := sq_le_pow2 t (by omega)
  have hd : d+e+1≤t := by omega
  have hmul := Nat.mul_le_mul_right t hd
  have hmul' : (d+e+1)*t=d*t+e*t+t := by grind only
  rw [hmul'] at hmul
  have ht1 : 1≤t := by omega
  have het := Nat.mul_le_mul_left e ht1
  simp at het
  have heq : d*(t+1)=d*t+d := by grind only
  have hexp : e+d*(t+1)<n := by rw [heq]; omega
  have hnlt := (log_window n hnpos).1
  change n<2^(t+1) at hnlt
  have hpow := Nat.pow_le_pow_left (Nat.le_of_lt hnlt) d
  have hm := Nat.mul_le_mul_left (2^e) hpow
  rw [←Nat.pow_mul,←Nat.pow_add,Nat.mul_comm (t+1) d] at hm
  have hstrict := Nat.pow_lt_pow_right (show 1<2 by decide) hexp
  exact Nat.lt_of_le_of_lt hm hstrict

def coefficientThreshold (A d : Nat) := expThreshold (A.log2+1) d

theorem coefficient_dom (A d n : Nat) (hn : coefficientThreshold A d≤n) : A*n^d<2^n := by
  have hA : A≤2^(A.log2+1) := by
    by_cases h0 : A=0
    · simp [h0]
    · exact Nat.le_of_lt (log_window A (by omega)).1
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (n^d) hA) (exp_dom (A.log2+1) d n hn)

#print axioms exp_dom
#print axioms coefficient_dom
/-- Coefficient update for the polynomial error envelope. -/
def scaleCoeff (D B C : Nat) : Nat := 2*D*(B+C)
def nextCoeff (D B C : Nat) : Nat := scaleCoeff D B C*(2*C+2)
def gapCoeff (D M B C : Nat) : Nat := D*M*scaleCoeff D B C*(nextCoeff D B C+C+8)

theorem generic_scale (n D M B C p : Nat) (hn : 1≤n)
    (hD : 0<D) (hM : 0<M) (hB : 0<B) (hp : 1≤p)
    (hdom : coefficientThreshold (gapCoeff D M B C) (2*p+1)≤n) :
    ∃ ell : Nat,
      2^ell≤2^n ∧ D*(B*n^p+C*n)<2^ell ∧
      D*M*2^ell*(2^ell*(2*(C*n)+2)+C*n+8)<2^n ∧
      2^ell*(2*(C*n)+2)≤nextCoeff D B C*n^(p+1) := by
  let X := D*(B*n^p+C*n)
  let ell := X.log2+1
  let S := 2^ell
  let A := scaleCoeff D B C
  let B' := nextCoeff D B C
  have hnp : n≤n^p := by simpa using Nat.pow_le_pow_right (show 0<n by omega) hp
  have hnpp : n≤n^(p+1) := by simpa using Nat.pow_le_pow_right (show 0<n by omega) (show 1≤p+1 by omega)
  have hX : 0<X := by
    have h1 : 0<B*n^p := Nat.mul_pos hB (Nat.pow_pos (by omega))
    exact Nat.mul_pos hD (by omega)
  obtain ⟨hXS,hSX⟩ := log_window X hX
  change X<S at hXS
  change S≤2*X at hSX
  have hS : S≤A*n^p := by
    have hcn := Nat.mul_le_mul_left C hnp
    have hsum : B*n^p+C*n≤(B+C)*n^p := by rw [Nat.add_mul]; omega
    have hm := Nat.mul_le_mul_left (2*D) hsum
    have he : (2*D)*(B*n^p+C*n)=2*X := by dsimp [X]; ac_rfl
    rw [he] at hm
    exact Nat.le_trans hSX (by simpa [A,scaleCoeff,Nat.mul_assoc] using hm)
  have hE : S*(2*(C*n)+2)≤B'*n^(p+1) := by
    have hc : 2*(C*n)+2≤(2*C+2)*n := by
      have he : (2*C+2)*n=2*(C*n)+2*n := by grind only
      rw [he]
      omega
    have hm := Nat.mul_le_mul hS hc
    have he : A*n^p*((2*C+2)*n)=B'*n^(p+1) := by
      rw [Nat.pow_succ]
      dsimp [B',nextCoeff,A]
      ac_rfl
    rwa [he] at hm
  have hmargin : C*n+8≤(C+8)*n^(p+1) := by
    have h1 := Nat.mul_le_mul_left C hnpp
    have h2 : 1≤n^(p+1) := by omega
    rw [Nat.add_mul]
    omega
  have hsum : S*(2*(C*n)+2)+C*n+8≤(B'+C+8)*n^(p+1) := by
    rw [Nat.add_mul,Nat.add_mul]
    rw [Nat.add_mul] at hmargin
    omega
  have h1 := Nat.mul_le_mul_left (D*M) hS
  have h2 := Nat.mul_le_mul h1 hsum
  have he : D*M*(A*n^p)*((B'+C+8)*n^(p+1))=gapCoeff D M B C*n^(2*p+1) := by
    calc
      D*M*(A*n^p)*((B'+C+8)*n^(p+1)) = gapCoeff D M B C*(n^p*n^(p+1)) := by dsimp [gapCoeff,A,B']; ac_rfl
      _ = _ := by rw [←Nat.pow_add,show p+(p+1)=2*p+1 by omega]
  rw [he] at h2
  have hgap := Nat.lt_of_le_of_lt h2 (coefficient_dom (gapCoeff D M B C) (2*p+1) n hdom)
  have hSle : S≤2^n := by
    have hDM : 1≤D*M := by have := Nat.mul_pos hD hM; omega
    have hm := Nat.mul_le_mul_right S hDM
    simp only [Nat.one_mul] at hm
    have hs : 1≤S*(2*(C*n)+2)+C*n+8 := by omega
    have hm' := Nat.mul_le_mul_left (D*M*S) hs
    simp only [Nat.mul_one] at hm'
    exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_trans hm hm') hgap)
  exact ⟨ell,hSle,hXS,hgap,hE⟩

#print axioms generic_scale
end BB6.Agent9Renewal
