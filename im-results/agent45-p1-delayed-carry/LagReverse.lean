import LagChecker
namespace BB6.Agent45.DelayedCarry

/-- Fixed-target carry steps have unique predecessor and bit. -/
theorem inverse_digit (C a x c y : Nat) (hC : 0<C) (ha : a<C)
    (he : 2*c+y=a+x*C) : (2*c+y)%C=a ∧ (2*c+y)/C=x := by
  rw [he,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt ha,Nat.add_mul_div_right _ _ hC,Nat.div_eq_of_lt ha,Nat.zero_add]
  exact ⟨rfl,rfl⟩

def predecessor (n B i c : Nat) := (2*c+target n i B)%(n+i+3)
def reverseDigit (n B i c : Nat) := (2*c+target n i B)/(n+i+3)

/-- Unique reverse prefix recovery using the known delayed bits of B. -/
def recover (n B s : Nat) : Nat → Nat → Nat × Nat
  | 0,c => (B,c)
  | k+1,c =>
    let p := recover n B s k (predecessor n B (s+k) c)
    (p.1+2^(s+k)*reverseDigit n B (s+k) c,p.2)

theorem recover_exact (n s B a k C c : Nat) (htr : Trace n s B a)
    (he : Extend n s B a k C c) (hk : k≤n) : recover n B s k c=(C,a) := by
  induction he with
  | nil => rfl
  | step k C c x d h hx he ih =>
    have hpre := extend_trace n s B a k C c htr h
    have ha := (trace_bounds n _ _ _ hpre).2.2.2
    obtain ⟨R,hR⟩ := extend_mod n s B a k C c h
    have hy := target_prefix n s (s+k) B R (by omega)
    rw [← hR] at hy
    have hEq : 2*d+target n (s+k) B=c+x*(n+(s+k)+3) := by rw [← hy]; exact he
    obtain ⟨hp,hd⟩ := inverse_digit (n+(s+k)+3) c x d (target n (s+k) B) (by omega) (by omega) hEq
    simp only [recover,predecessor,reverseDigit,hp,hd,ih (by omega)]

/-- Recover only the ancestor carry at the start of a suffix. -/
def rewind (n B s : Nat) : Nat → Nat → Nat
  | 0,c => c
  | k+1,c => rewind n B s k (predecessor n B (s+k) c)

theorem extend_split (n s B a k C c h : Nat) (he : Extend n s B a k C c)
    (hh : h≤k) : ∃ D d, Extend n s B a h D d ∧ Extend n (s+h) D d (k-h) C c := by
  induction he with
  | nil => have hz : h=0 := by omega
           subst h; exact ⟨B,a,Extend.nil,by simpa using (Extend.nil : Extend n s B a 0 B a)⟩
  | step k C c x d he hx hEq ih =>
    by_cases hk : h≤k
    · obtain ⟨D,e,hpre,hsuf⟩ := ih hk
      have hidx : s+h+(k-h)=s+k := by omega
      have hlen : k+1-h=k-h+1 := by omega
      refine ⟨D,e,hpre,?_⟩
      rw [hlen]
      have hhEq : 2*d+target n (s+h+(k-h)) C=c+x*(n+(s+h+(k-h))+3) := by simpa [hidx] using hEq
      simpa only [hidx] using Extend.step (k-h) C c x d hsuf hx hhEq
    · have hke : h=k+1 := by omega
      subst h
      refine ⟨_,_,Extend.step k C c x d he hx hEq,?_⟩
      simpa using (Extend.nil : Extend n (s+(k+1)) (C+2^(s+k)*x) d 0 (C+2^(s+k)*x) d)

/-- If a suffix lies within a known target window, its end determines
its start carry without reading any of its newly appended bits. -/
theorem rewind_exact (n s B a h D d j C c : Nat) (htr : Trace n s B a)
    (hpre : Extend n s B a h D d) (hsuf : Extend n (s+h) D d j C c)
    (hj : h+j≤n) : rewind n B (s+h) j c=d := by
  induction hsuf with
  | nil => rfl
  | step k C c x e hsuf hx hEq ih =>
    have hfull := extend_append n s B a h D d k C c hpre hsuf
    have htrace := extend_trace n s B a (h+k) C c htr hfull
    have hc := (trace_bounds n _ _ _ htrace).2.2.2
    obtain ⟨R,hR⟩ := extend_mod n s B a (h+k) C c hfull
    have hy := target_prefix n s (s+h+k) B R (by omega)
    rw [← hR] at hy
    have hEq' : 2*e+target n (s+h+k) B=c+x*(n+(s+h+k)+3) := by rw [← hy]; exact hEq
    obtain ⟨hp,hd⟩ := inverse_digit (n+(s+h+k)+3) c x e (target n (s+h+k) B) (by omega) (by omega) hEq'
    simp only [rewind,predecessor,hp,ih (by omega)]

#print axioms recover_exact
#print axioms rewind_exact
end BB6.Agent45.DelayedCarry
