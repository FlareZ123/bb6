import HalfBlockMargin

namespace BB6.Agent43P1Complement
open BB6.Agent45.DelayedCarry

/-- At position i these two words record whether the g-bit window
    beginning there has a one, and whether every bit is one. -/
def windowOr (X : Nat) : Nat → Nat
  | 0 => 0
  | g+1 => X ||| (windowOr X g >>> 1)

def windowAnd (X : Nat) : Nat → Nat
  | 0 => X
  | g+1 => X &&& (windowAnd X g >>> 1)

/-- One extra bit is used for windowAnd's seed; take g-1 iterations. -/
theorem windowOr_sound (X g i : Nat) (h : (windowOr X g).testBit i=true) :
    ∃ k, k<g ∧ X.testBit (i+k)=true := by
  induction g generalizing i with
  | zero => simp [windowOr] at h
  | succ g ih =>
    simp only [windowOr,Nat.testBit_or,Nat.testBit_shiftRight,Bool.or_eq_true] at h
    rcases h with h|h
    · exact ⟨0,by omega,by simpa using h⟩
    · obtain ⟨k,hk,hbit⟩ := ih (1+i) h
      exact ⟨k+1,by omega,by simpa [show i+(k+1)=1+i+k by omega] using hbit⟩

theorem windowAnd_sound (X g i : Nat) (h : (windowAnd X g).testBit i=false) :
    ∃ k, k≤g ∧ X.testBit (i+k)=false := by
  induction g generalizing i with
  | zero => exact ⟨0,by omega,by simpa [windowAnd] using h⟩
  | succ g ih =>
    simp only [windowAnd,Nat.testBit_and,Nat.testBit_shiftRight,Bool.and_eq_false_iff] at h
    rcases h with h|h
    · exact ⟨0,by omega,by simpa using h⟩
    · obtain ⟨k,hk,hbit⟩ := ih (1+i) h
      exact ⟨k+1,by omega,by simpa [show i+(k+1)=1+i+k by omega] using hbit⟩

/-- All length-g windows inside the t-bit low product must contain both bits. -/
def RunOK (t g X : Nat) : Prop :=
  0<g ∧ (windowOr X g &&& (2^(t-g+1)-1))=2^(t-g+1)-1 ∧
    (windowAnd X (g-1) &&& (2^(t-g+1)-1))=0

theorem runOK_bits (t g X i : Nat) (h : RunOK t g X) (hi : i+g≤t) :
    (∃ k, k<g ∧ X.testBit (i+k)=true) ∧
    (∃ k, k<g ∧ X.testBit (i+k)=false) := by
  obtain ⟨hg,hor,hand⟩ := h
  have hm : (2^(t-g+1)-1).testBit i=true := by
    rw [Nat.testBit_two_pow_sub_one]; simp [show i<t-g+1 by omega]
  have ho := congrArg (fun x : Nat => x.testBit i) hor
  have ha := congrArg (fun x : Nat => x.testBit i) hand
  simp [show i<t-g+1 by omega] at ho ha
  refine ⟨windowOr_sound X g i ho,?_⟩
  obtain ⟨k,hk,hb⟩ := windowAnd_sound X (g-1) i ha
  exact ⟨k,by omega,hb⟩

/-- A mixed high window forces the distance from both endpoints to be
    at least 2^(j-g). This avoids computing a giant product at every prefix. -/
theorem mixed_margin (j g X : Nat) (_hg : 0<g) (hj : g≤j)
    (h1 : ∃ k, k<g ∧ X.testBit (j-g+k)=true)
    (h0 : ∃ k, k<g ∧ X.testBit (j-g+k)=false) :
    2^(j-g)≤min (X%2^j) (2^j-X%2^j) := by
  let D := 2^(j-g)
  let z := X%2^j
  let q := z/D
  have hD : 0<D := Nat.two_pow_pos _
  have hpow : 2^j=D*2^g := by dsimp [D]; rw [←Nat.pow_add]; congr 1; omega
  have hz : z<2^j := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hq : q<2^g := by
    dsimp [q]; apply (Nat.div_lt_iff_lt_mul hD).2
    simpa [hpow,Nat.mul_comm] using hz
  have hbit (k : Nat) (hk : k<g) : q.testBit k = X.testBit (j-g+k) := by
    dsimp [q,z,D]
    rw [←Nat.shiftRight_eq_div_pow,Nat.testBit_shiftRight,Nat.testBit_mod_two_pow]
    simp [show j-g+k<j by omega]
  have hpos : 0<q := by
    obtain ⟨k,hk,hb⟩ := h1
    have ht := hbit k hk
    by_cases hq0 : q=0
    · simp [hq0,hb] at ht
    · exact Nat.pos_of_ne_zero hq0
  have htop : q+1<2^g := by
    obtain ⟨k,hk,hb⟩ := h0
    have ht := hbit k hk
    by_cases hqtop : q=2^g-1
    · rw [hqtop,Nat.testBit_two_pow_sub_one] at ht
      simp [hk,hb] at ht
    · omega
  have hlo : D≤z := by
    have hmul := Nat.mul_le_mul_left D hpos
    have hdiv := Nat.div_add_mod z D
    have hm : D≤D*(z/D) := by simpa [q] using hmul
    omega
  have hup : z+D≤2^j := by
    have hmul := Nat.mul_le_mul_left D (show q+2≤2^g by omega)
    have hd := Nat.div_add_mod z D
    have hr := Nat.mod_lt z hD
    rw [Nat.mul_add,Nat.mul_succ,←Nat.add_assoc] at hmul
    rw [hpow]
    dsimp [q] at hmul
    omega
  exact Nat.le_min.mpr ⟨hlo,by omega⟩

/-- A single packed-window check proves the margin bound at every low prefix,
    including the initial short prefixes whose odd low bit prevents zero. -/
theorem runOK_resMin (t g C j : Nat) (ho : C%2=1) (hj : 1≤j) (hjt : j≤t)
    (h : RunOK t g (7*C)) : 2^(j-g)≤resMin j C := by
  by_cases hgj : g≤j
  · obtain ⟨h1,h0⟩ := runOK_bits t g (7*C) (j-g) h (by omega)
    exact mixed_margin j g (7*C) h.1 hgj h1 h0
  · have hd : 2 ∣ (2:Nat)^j := by simpa using Nat.pow_dvd_pow 2 hj
    have hm : ((7*C)%2^j)%2=1 := by rw [Nat.mod_mod_of_dvd _ hd,Nat.mul_mod]; simp [ho]
    have hlt : (7*C)%2^j<2^j := Nat.mod_lt _ (Nat.two_pow_pos _)
    rw [show j-g=0 by omega,Nat.pow_zero]
    unfold resMin
    exact Nat.le_min.mpr ⟨by omega,by omega⟩

theorem runOK_margin (n K t g C j : Nat) (ho : C%2=1) (hj : 1≤j) (hjt : j≤t)
    (h : RunOK t g (7*C)) (hgn : g≤n)
    (hsafe : (n+K+2)*marginSize n K<6*2^(n-g)) :
    (n+K+2)*marginSize n K*2^j<6*2^n*resMin j C := by
  have hmin := runOK_resMin t g C j ho hj hjt h
  have hmul := Nat.mul_lt_mul_of_pos_right hsafe (Nat.two_pow_pos j)
  have hexp : n-g+j≤n+(j-g) := by omega
  have hpow := Nat.pow_le_pow_right (show 0<2 by decide) hexp
  have hle : 6*2^(n-g)*2^j≤6*2^n*2^(j-g) := by
    rw [Nat.mul_assoc,←Nat.pow_add,Nat.mul_assoc,←Nat.pow_add]
    exact Nat.mul_le_mul_left 6 hpow
  exact Nat.lt_of_lt_of_le hmul (Nat.le_trans hle (Nat.mul_le_mul_left _ hmin))

/-- A checked list of odd candidates and their mixed-window bounds discharges
    all the margin obligations of the long midpoint certificate. -/
theorem allBlockMargins_of_runOK (n K s h g : Nat) (qs : List Prefix)
    (hgn : g≤n) (hsafe : (n+K+2)*marginSize n K<6*2^(n-g))
    (hcheck : ∀ C c, (C,c)∈qs → C%2=1 ∧ RunOK (s+h) g (7*C)) :
    AllBlockMargins n K s h qs := by
  intro C c hc j hj hjt
  obtain ⟨ho,hrun⟩ := hcheck C c hc
  exact runOK_margin n K (s+h) g C j ho (by omega) hjt hrun hgn hsafe

#print axioms runOK_bits
#print axioms mixed_margin
#print axioms runOK_resMin
#print axioms runOK_margin
#print axioms allBlockMargins_of_runOK
end BB6.Agent43P1Complement
