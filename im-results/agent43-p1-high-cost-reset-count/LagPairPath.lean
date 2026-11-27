import PackedRecover
namespace BB6.Agent43LagPair
open BB6.Agent45.DelayedCarry
open BB6.Agent43PackedRecover

def digit (n P q : Nat) := targetBit n (q-(n+3)) P
theorem digit_le (n P q : Nat) : digit n P q ≤ 1 := by
  unfold digit targetBit
  split <;> simp_all <;> split <;> simp

def Edge (n P q a b : Nat) := a<q ∧ b<q+1 ∧ ∃ x, x≤1 ∧ 2*b+digit n P q=a+x*q
inductive FixedWalk (n P : Nat) : Nat → Nat → Nat → Nat → Prop
  | nil (q a : Nat) (ha : a<q) : FixedWalk n P q a 0 a
  | cons (q a b k z : Nat) (he : Edge n P q a b)
      (tail : FixedWalk n P (q+1) b k z) : FixedWalk n P q a (k+1) z

theorem fixed_start {n P q a k z : Nat} (h : FixedWalk n P q a k z) : a<q := by
  cases h with
  | nil _ _ ha => exact ha
  | cons _ _ _ _ _ he _ => exact he.1
theorem fixed_first {n P q a k z : Nat} (h : FixedWalk n P q a (k+1) z) :
    ∃ b, Edge n P q a b := by
  cases h with
  | cons _ _ b _ _ he _ => exact ⟨b,he⟩
theorem fixed_append {n P q a k b : Nat} (h : FixedWalk n P q a k b) :
    ∀ j z, FixedWalk n P (q+k) b j z → FixedWalk n P q a (k+j) z := by
  induction h with
  | nil q a ha =>
    intro j z hz
    simpa using hz
  | cons q a b k c he ht ih =>
    intro j z hz
    have hz' : FixedWalk n P ((q+1)+k) c j z := by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hz
    have hh := FixedWalk.cons q a b (k+j) z he (ih j z hz')
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem fixed_suffix (n s B a h C c j D d : Nat)
    (htr : Trace n s B a) (hpre : Extend n s B a h C c)
    (hsuf : Extend n (s+h) C c j D d) (hj : h+j≤n) :
    FixedWalk n (7*B) (n+s+h+3) c j d := by
  have hc := extend_trace n s B a h C c htr hpre
  induction hsuf with
  | nil =>
    exact FixedWalk.nil _ _ (by have hb := (trace_bounds n _ _ _ hc).2.2.2; omega)
  | step k D d x e he hx hEq ih =>
    have hfull := extend_append n s B a h C c k D d hpre he
    have ht := extend_trace n s B a (h+k) D d htr hfull
    have hd := (trace_bounds n _ _ _ ht).2.2.2
    have ht' := extend_trace n (s+h) C c (k+1) (D+2^(s+h+k)*x) e hc
      (Extend.step k D d x e he hx hEq)
    have he' := (trace_bounds n _ _ _ ht').2.2.2
    obtain ⟨R,hR⟩ := extend_mod n s B a (h+k) D d hfull
    have hy := target_prefix n s (s+h+k) B R (by omega)
    rw [←hR] at hy
    have hEdge : Edge n (7*B) (n+s+h+3+k) d e := by
      refine ⟨by omega,by omega,x,hx,?_⟩
      unfold digit
      rw [show n+s+h+3+k-(n+3)=s+h+k by omega,targetBit_eq,←hy]
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hEq
    have hlast := FixedWalk.cons (n+s+h+3+k) d e 0 e hEdge
      (FixedWalk.nil _ _ (by omega))
    simpa using fixed_append (ih (by omega)) 1 e (by simpa using hlast)

theorem even_half (n P r a b : Nat) (he : Edge n P (2*r) a b) :
    a=2*(a/2)+digit n P (2*r) ∧ a/2<r ∧ b%r=a/2 := by
  obtain ⟨ha,hb,x,hx,hEq⟩ := he
  have hy := digit_le n P (2*r)
  have hhalf : a/2<r := by omega
  rcases (show x=0∨x=1 by omega) with rfl|rfl
  · simp at hEq
    have hp : a=2*(a/2)+digit n P (2*r) := by omega
    have h : b=a/2 := by omega
    exact ⟨hp,hhalf,by rw [h,Nat.mod_eq_of_lt hhalf]⟩
  · simp at hEq
    have hp : a=2*(a/2)+digit n P (2*r) := by omega
    have h : b=a/2+r := by omega
    exact ⟨hp,hhalf,by rw [h,Nat.add_mod_right,Nat.mod_eq_of_lt hhalf]⟩

def shift (n P r : Nat) := 2*digit n P (2*r+2)+digit n P (2*r+1)
theorem pair_parent (n P r a b c d : Nat)
    (h0 : Edge n P (2*r) a b) (h1 : Edge n P (2*r+1) b c)
    (h2 : Edge n P (2*r+2) c d) :
    a/2<r ∧ c/2<r+1 ∧ 4*(c/2)+shift n P r<4*r+2 ∧
      ((4*(c/2)+shift n P r)%(2*r+1))%r=a/2 := by
  obtain ⟨hp,ha,hm⟩ := even_half n P r a b h0
  have h2' : Edge n P (2*(r+1)) c d := by simpa [Nat.mul_add] using h2
  obtain ⟨hc,hcb,_⟩ := even_half n P (r+1) c d h2'
  obtain ⟨hb,_,x,hx,he⟩ := h1
  have hce : c=2*(c/2)+digit n P (2*r+2) := by simpa [Nat.mul_add] using hc
  have hu : 4*(c/2)+shift n P r=2*c+digit n P (2*r+1) := by unfold shift; omega
  have hmod := (inverse_digit (2*r+1) b x c (digit n P (2*r+1)) (by omega) hb he).1
  refine ⟨ha,hcb,?_,?_⟩
  · rw [hu,he]
    rcases (show x=0∨x=1 by omega) with rfl|rfl <;> simp <;> omega
  · rw [hu,hmod,hm]
theorem path_pair {n P r a k z : Nat} (h : FixedWalk n P (2*r) a (k+3) z) :
    ∃ c, FixedWalk n P (2*r+2) c (k+1) z ∧ a/2<r ∧ c/2<r+1 ∧
      4*(c/2)+shift n P r<4*r+2 ∧ ((4*(c/2)+shift n P r)%(2*r+1))%r=a/2 := by
  cases h with
  | cons _ _ b _ _ he tail =>
    cases tail with
    | cons _ _ c _ _ he' tail' =>
      have ht : FixedWalk n P (2*r+2) c (k+1) z := by simpa [Nat.add_assoc] using tail'
      obtain ⟨d,he''⟩ := fixed_first ht
      exact ⟨c,ht,pair_parent n P r a b c d he he' he''⟩
#print axioms fixed_suffix
#print axioms pair_parent
end BB6.Agent43LagPair
