import FastSectionDef
import Lean.Elab.Tactic.Omega

namespace BB6.Agent12ClosedBounce
open BB6.Agent46

-- b=3 for odd, 4 for even. The same power bound gives the first exit.
def stop (b k c n : Nat) : Prop :=
  c+2*k+3*n+2*b ≤ 2^(n+2)*(k+b)

def middle (b k n : Nat) : Nat := 2^n*(k+b)-b

def high (b k c n : Nat) : Nat := c+2*k+3*n-2*middle b k n

def First (b k c n : Nat) : Prop :=
  stop b k c n ∧ ∀ j, j<n → ¬stop b k c j

theorem stop_zero (b k c : Nat) : stop b k c 0 ↔ c≤2*k+2*b := by
  simp [stop]; omega

theorem stop_shift (b k c n : Nat) (hb : b=3 ∨ b=4)
    (hc : 2*k+2*b<c) :
    stop b (2*k+b) (c-(2*k+2*b-3)) n ↔ stop b k c (n+1) := by
  unfold stop
  have he : 2^(n+2)*(2*k+b+b)=2^(n+1+2)*(k+b) := by
    rw [show 2*k+b+b=2*(k+b) by omega,show n+1+2=n+2+1 by omega]
    simp only [Nat.pow_succ]
    ac_rfl
  rw [he]
  omega

theorem middle_shift (b k n : Nat) : middle b (2*k+b) n = middle b k (n+1) := by
  unfold middle
  rw [Nat.pow_succ, show 2*k+b+b=2*(k+b) by omega,Nat.mul_assoc]

theorem high_shift (b k c n : Nat) (hb : b=3 ∨ b=4)
    (hc : 2*k+2*b<c) :
    high b (2*k+b) (c-(2*k+2*b-3)) n = high b k c (n+1) := by
  unfold high
  rw [middle_shift]
  omega

theorem First.shift (b k c n : Nat) (hb : b=3 ∨ b=4)
    (h : First b k c (n+1)) : 2*k+2*b<c ∧
    First b (2*k+b) (c-(2*k+2*b-3)) n := by
  have h0 := h.2 0 (by omega)
  rw [stop_zero] at h0
  have hc : 2*k+2*b<c := by omega
  refine ⟨hc, (stop_shift b k c n hb hc).2 h.1, ?_⟩
  intro j hj hs
  exact h.2 (j+1) (by omega) ((stop_shift b k c j hb hc).1 hs)

theorem odd_closed (k c n : Nat) (ho : k%2=1) (hc : 4≤c)
    (h : First 3 k c n) :
    bounce k c = (c+n, some (2*middle 3 k n+6-high 3 k c n,high 3 k c n)) := by
  induction n generalizing k c with
  | zero =>
    have hs := (stop_zero 3 k c).1 h.1
    rw [bounce.eq_1]
    simp [ho,show ¬c<4 by omega,show c≤2*k+6 by omega,middle,high]
  | succ n ih =>
    obtain ⟨hs,hn⟩ := h.shift 3 k c n (Or.inl rfl)
    have hs' : ¬c≤2*k+6 := by omega
    have hn' : First 3 (2*k+3) (c-(2*k+3)) n := by simpa using hn
    have hi := ih (2*k+3) (c-(2*k+3)) (by omega) (by omega) hn'
    rw [bounce.eq_1]
    simp only [show ¬c<4 by omega,ite_false,ho,ite_true,hs']
    rw [hi,middle_shift,show high 3 (2*k+3) (c-(2*k+3)) n = high 3 k c (n+1) from high_shift 3 k c n (Or.inl rfl) hs]
    simp
    omega

-- Clock convention: even ordinary / terminal c=5 costs c-2*n-3;
-- exceptional c=4 adds exactly one to that expression.
def evenResult (k c n : Nat) : Nat × Option (Nat × Nat) :=
  let K := middle 4 k n
  let C := high 4 k c n
  if C=4 then (c-2*n-2,some (2*K+2,3))
  else if C=5 then (c-2*n-3,none)
  else (c-2*n-3,some (2*K+8-C,C-1))

theorem even_depth_bound (k c n : Nat) (hc : 4≤c) (h : First 4 k c n) :
    2*n+4≤c := by
  induction n generalizing k c with
  | zero => omega
  | succ n ih =>
    obtain ⟨hs,hn⟩ := h.shift 4 k c n (Or.inr rfl)
    have hn' : First 4 (2*k+4) (c-(2*k+5)) n := by simpa using hn
    have hi := ih (2*k+4) (c-(2*k+5)) (by omega) hn'
    omega

theorem even_closed (k c n : Nat) (ho : k%2=0) (hc : 4≤c)
    (h : First 4 k c n) : bounce k c = evenResult k c n := by
  induction n generalizing k c with
  | zero =>
    have hs := (stop_zero 4 k c).1 h.1
    rw [bounce.eq_1]
    simp only [show ¬c<4 by omega,ite_false,show ¬k%2=1 by omega]
    have hm : middle 4 k 0=k := by simp [middle]
    have hC : high 4 k c 0=c := by simp [high,hm]
    simp only [evenResult,hm,hC,Nat.mul_zero,Nat.sub_zero]
    split <;> simp_all <;> omega
  | succ n ih =>
    obtain ⟨hs,hn⟩ := h.shift 4 k c n (Or.inr rfl)
    have hn' : First 4 (2*k+4) (c-(2*k+5)) n := by simpa using hn
    have hi := ih (2*k+4) (c-(2*k+5)) (by omega) (by omega) hn'
    have hbound := even_depth_bound (2*k+4) (c-(2*k+5)) n (by omega) hn'
    rw [bounce.eq_1]
    simp only [show ¬c<4 by omega,show ¬k%2=1 by omega,show c≠4 by omega,show c≠5 by omega,show ¬c≤2*k+8 by omega,ite_false]
    rw [hi]
    simp only [evenResult,middle_shift,show high 4 (2*k+4) (c-(2*k+5)) n = high 4 k c (n+1) from high_shift 4 k c n (Or.inr rfl) hs]
    split <;> simp_all <;> try omega
    split <;> simp_all <;> omega

-- Estimate the first exit depth from two binary logarithms.
def lowDepth (b k c : Nat) : Nat := (c+2*(k+b)).log2 - (k+b).log2 - 2

theorem depth_lower (b k c n : Nat) (hb : 3≤b)
    (hn : n<lowDepth b k c) : ¬stop b k c n := by
  let B := k+b
  let N := c+2*B
  have hB : B≠0 := by dsimp [B]; omega
  have hN : N≠0 := by dsimp [N,B]; omega
  have h1 : B<2^(B.log2+1) := Nat.lt_log2_self
  have h2 : 2^N.log2≤N := Nat.log2_self_le hN
  have h3 : n+2+(B.log2+1)≤N.log2 := by
    change n<N.log2-B.log2-2 at hn
    omega
  have h4 := Nat.pow_le_pow_right (by decide : 0<2) h3
  rw [Nat.pow_add] at h4
  have h5 := Nat.mul_lt_mul_of_pos_left h1 (Nat.pow_pos (by decide : 0<2)) (k := 2^(n+2))
  have hh : 2^(n+2)*B<N := Nat.lt_of_lt_of_le h5 (Nat.le_trans h4 h2)
  change ¬(c+2*k+3*n+2*b≤2^(n+2)*B)
  dsimp [N,B] at hh
  omega

private theorem three_log_bound (n : Nat) : 3*(n-1)≤2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    cases n with
    | zero => decide
    | succ n =>
      cases n with
      | zero => decide
      | succ n => omega

-- At most two increments beyond the logarithmic lower bound suffice.
theorem depth_upper_two (b k c : Nat) (hb : 3≤b) : stop b k c (lowDepth b k c+2) := by
  let B := k+b
  let N := c+2*B
  let n := lowDepth b k c+2
  have hB : 3≤B := by dsimp [B]; omega
  have hN : 6≤N := by dsimp [N,B]; omega
  have hB0 : B≠0 := by omega
  have hN0 : N≠0 := by omega
  have hlB : 1≤B.log2 := (Nat.le_log2 hB0).2 (by omega : 2^1≤B)
  have hp : N.log2≤n+B.log2 := by
    change N.log2≤N.log2-B.log2-2+2+B.log2
    omega
  have hlow : 2^B.log2≤B := Nat.log2_self_le hB0
  have hpow : 2^(N.log2+2)≤2^(n+2+B.log2) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.pow_add 2 (n+2)] at hpow
  have hm := Nat.mul_le_mul_left (2^(n+2)) hlow
  have hP : 2^N.log2*4≤2^(n+2)*B := by
    have h4 : 2^(N.log2+2)=2^N.log2*4 := by rw [Nat.pow_add]
    rw [h4] at hpow
    exact Nat.le_trans hpow hm
  have hNlt : N<2^N.log2*2 := by
    rw [←Nat.pow_succ]
    exact Nat.lt_log2_self
  have hNge : 2^N.log2≤N := Nat.log2_self_le hN0
  have h3 := three_log_bound N.log2
  have hn : n≤2 ∨ n≤N.log2-1 := by
    change N.log2-B.log2-2+2≤2 ∨ N.log2-B.log2-2+2≤N.log2-1
    omega
  have h3n : 3*n≤N := by omega
  change c+2*k+3*n+2*b≤2^(n+2)*B
  dsimp [N,B] at *
  omega

instance (b k c n : Nat) : Decidable (stop b k c n) := inferInstanceAs (Decidable (_ ≤ _))

def searchDepth (b k c : Nat) : Nat → Nat → Nat
  | start,0 => start
  | start,fuel+1 => if stop b k c start then start else searchDepth b k c (start+1) fuel

theorem searchDepth_first (b k c start fuel : Nat)
    (hprev : ∀ j, j<start → ¬stop b k c j)
    (hend : stop b k c (start+fuel)) : First b k c (searchDepth b k c start fuel) := by
  induction fuel generalizing start with
  | zero => simpa [searchDepth,First] using And.intro (by simpa using hend : stop b k c start) hprev
  | succ fuel ih =>
    by_cases h : stop b k c start
    · simpa [searchDepth,h,First] using And.intro h hprev
    · simp [searchDepth,h]
      apply ih
      · intro j hj
        by_cases he : j=start
        · simpa [he] using h
        · exact hprev j (by omega)
      · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hend

def depth (b k c : Nat) : Nat :=
  searchDepth b k c (lowDepth b k c) 2

theorem depth_first (b k c : Nat) (hb : 3≤b) : First b k c (depth b k c) := by
  unfold depth
  apply searchDepth_first
  · intro j hj
    exact depth_lower b k c j hb hj
  · exact depth_upper_two b k c hb

def closedBounce (k c : Nat) : Nat × Option (Nat × Nat) :=
  if c<4 then (0,none)
  else if k%2=1 then
    let n := depth 3 k c
    (c+n, some (2*middle 3 k n+6-high 3 k c n,high 3 k c n))
  else evenResult k c (depth 4 k c)

theorem closedBounce_eq (k c : Nat) : closedBounce k c=bounce k c := by
  unfold closedBounce
  split
  next h => rw [bounce.eq_1]; simp [h]
  next h =>
    split
    next ho => exact (odd_closed k c _ ho (by omega) (depth_first 3 k c (by decide))).symm
    next he => exact (even_closed k c _ (by omega) (by omega) (depth_first 4 k c (by decide))).symm

def closedSection (p : Nat × Nat) : Nat × Option (Nat × Nat) :=
  let (a,k) := p
  if a=0 then
    if k=0 then (2,none)
    else if k=1 then (4,some (0,4))
    else
      let b := closedBounce 1 (2*k+1)
      (2+b.1,b.2)
  else if a=1 then
    if k=0 then (2,some (5,1))
    else if k=1 then (2,some (2,3))
    else if k=2 then (3,some (2,5))
    else if k=3 then (5,some (0,7))
    else
      let b := closedBounce 4 (2*k-3)
      (3+b.1,b.2)
  else if k=0 then (2,some (a-2,2))
  else if 2*k≤a then (2*k+1,some (a-2*k,2*k+2))
  else
    let b := closedBounce (a-1) (2*k-a+3)
    (a-1+b.1,b.2)

theorem closedSection_eq (p : Nat × Nat) : closedSection p=exactSection p := by
  rcases p with ⟨a,k⟩
  simp only [closedSection,exactSection,closedBounce_eq]

#print axioms closedBounce_eq
#print axioms closedSection_eq
end BB6.Agent12ClosedBounce
