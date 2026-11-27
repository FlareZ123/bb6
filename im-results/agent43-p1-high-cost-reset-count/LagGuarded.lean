import LagExact

namespace BB6.Agent43LagExact
open BB6.P1CarryExact (Micro LegalGap)

/-- Exact unit-cost guard language. A selected bit starts a complete gap
    only if the previous left coordinate is at least ten. The current
    right coordinate must remain at least two throughout its tail.
    The last gap need not yet be complete (left coordinate can be five). -/
inductive GuardedMicro (n : Nat) : Nat → Nat → Nat → Prop
  | root : GuardedMicro n 0 1 (BB6.P1CarryExact.total n-n-2)
  | one (m v w u z : Nat) (h : GuardedMicro n m v w)
      (hs : 10≤w) (hu : 2≤u)
      (hv : v+BB6.P1CarryExact.total n=2*u+(n+m+3)) (hw : w=2*z) :
      GuardedMicro n (m+1) u z
  | zero (m v w u z : Nat) (h : GuardedMicro n m v w)
      (hm : 0<m) (hu : 2≤u)
      (hv : v=2*u) (hw : w+BB6.P1CarryExact.total n=2*z+(n+m+3)) :
      GuardedMicro n (m+1) u z

theorem guarded_micro {n m v w : Nat} (h : GuardedMicro n m v w) :
    Micro n m v w := by
  induction h with
  | root => exact Micro.root
  | one m v w u z h hs hu hv hw ih => exact Micro.one m v w u z ih hv hw
  | zero m v w u z h hm hu hv hw ih => exact Micro.zero m v w u z ih hm hv hw

/-- A gap currently being expanded may have a temporarily small left
    coordinate. Its previous complete gaps already satisfy all guards. -/
inductive OpenGap (n : Nat) : Nat → Nat → Nat → Prop
  | root : OpenGap n 0 1 (BB6.P1CarryExact.total n-n-2)
  | edge (m v w e u z : Nat)
      (h : LegalGap n m v w) (he : 0<e)
      (hs : 10≤w ∧ w%2=0) (hu : 2≤u)
      (hm : u+z+n+(m+e)+1=BB6.P1CarryExact.total n)
      (hr : v+BB6.P1CarryExact.total n=2^e*u+(n+m+3)) :
      OpenGap n (m+e) u z

theorem close_gap {n m v w : Nat} (h : OpenGap n m v w) (hw : 6≤w) :
    LegalGap n m v w := by
  cases h with
  | root => exact LegalGap.root
  | edge s u z e v w h he hs hu hm hr =>
    exact LegalGap.edge s u z e v w h he hs ⟨hu,hw⟩ hm hr

theorem guarded_open {n m v w : Nat} (hn : 14≤n) (h : GuardedMicro n m v w) :
    OpenGap n m v w := by
  induction h with
  | root => exact OpenGap.root
  | one m v w u z h hs hu hv hw ih =>
    have hp := close_gap ih (by omega)
    have hm := BB6.P1CarryExact.micro_mass n (m+1) u z hn
      (guarded_micro (GuardedMicro.one m v w u z h hs hu hv hw))
    exact OpenGap.edge m v w 1 u z hp (by decide) ⟨hs,by omega⟩ hu hm
      (by simpa using hv)
  | zero m v w u z h hm hu hv hw ih =>
    have hmass := BB6.P1CarryExact.micro_mass n (m+1) u z hn
      (guarded_micro (GuardedMicro.zero m v w u z h hm hu hv hw))
    cases ih with
    | root => omega
    | edge s p q e v w hp he hs hprev hmass0 hr =>
      have hrec : p+BB6.P1CarryExact.total n=2^(e+1)*u+(n+s+3) := by
        rw [Nat.pow_succ,Nat.mul_assoc,←hv]
        exact hr
      have hmass' : u+z+n+(s+(e+1))+1=BB6.P1CarryExact.total n := by omega
      have hout := OpenGap.edge s p q (e+1) u z hp (by omega) hs hu hmass' hrec
      simpa [Nat.add_assoc] using hout

theorem guarded_extend_zeros (n m v w k u z : Nat) (hn : 14≤n)
    (hm : 0<m) (h : GuardedMicro n m v w) (hu : 2≤u)
    (hp : v=2^k*u)
    (hmass : u+z+n+(m+k)+1=BB6.P1CarryExact.total n) :
    GuardedMicro n (m+k) u z := by
  induction k generalizing m v w with
  | zero =>
    have hm0 := BB6.P1CarryExact.micro_mass n m v w hn (guarded_micro h)
    simp at hp hmass ⊢
    have hw : w=z := by omega
    simpa [hp,hw] using h
  | succ k ih =>
    let a := 2^k*u
    let b := w+a-1
    have hpow : 1≤2^k := Nat.one_le_pow _ _ (by decide)
    have ha : 2≤a := by
      have hmul := Nat.mul_le_mul_right u hpow
      dsimp [a]
      simpa using Nat.le_trans hu (by simpa using hmul : u≤2^k*u)
    have hV : v=2*a := by
      dsimp [a]
      rw [hp,Nat.pow_succ]
      ac_rfl
    have hm0 := BB6.P1CarryExact.micro_mass n m v w hn (guarded_micro h)
    have hW : w+BB6.P1CarryExact.total n=2*b+(n+m+3) := by dsimp [b]; omega
    have hnext := GuardedMicro.zero m v w a b h hm ha hV hW
    have hmass' : u+z+n+(m+1+k)+1=BB6.P1CarryExact.total n := by omega
    have hfin := ih (m+1) a b (by omega) hnext rfl hmass'
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hfin

theorem legal_to_guarded {n m v w : Nat} (hn : 14≤n) (h : LegalGap n m v w) :
    GuardedMicro n m v w := by
  induction h with
  | root => exact GuardedMicro.root
  | edge m v w e u z h he hs hu hm hr ih =>
    let k := e-1
    let a := 2^k*u
    let b := w/2
    have hE : k+1=e := by dsimp [k]; omega
    have hpow : 2^e*u=2*a := by rw [←hE,Nat.pow_succ]; dsimp [a]; ac_rfl
    have hV : v+BB6.P1CarryExact.total n=2*a+(n+m+3) := by rw [hr,hpow]
    have hW : w=2*b := by dsimp [b]; omega
    have ha : 2≤a := by
      have h1 : 1≤2^k := Nat.one_le_pow _ _ (by decide)
      have h2 := Nat.mul_le_mul_right u h1
      dsimp [a]
      simpa using Nat.le_trans hu.1 (by simpa using h2 : u≤2^k*u)
    have hnext := GuardedMicro.one m v w a b ih hs.1 ha hV hW
    have hm' : u+z+n+(m+1+k)+1=BB6.P1CarryExact.total n := by omega
    have hfin := guarded_extend_zeros n (m+1) a b k u z hn (by omega) hnext hu.1 rfl hm'
    have heq : m+1+k=m+e := by omega
    simpa [heq] using hfin

/-- The source guards are exactly recoverable at arbitrary cost.
    The terminal left bound is the only extra closing requirement. -/
theorem legal_iff_guarded {n m v w : Nat} (hn : 14≤n) :
    LegalGap n m v w ↔ GuardedMicro n m v w ∧ (m=0 ∨ 6≤w) := by
  constructor
  · intro h
    refine ⟨legal_to_guarded hn h,?_⟩
    cases h with
    | root => exact Or.inl rfl
    | edge _ _ _ _ _ _ _ _ _ he _ _ => exact Or.inr he.2
  · rintro ⟨h,hm|hw⟩
    · subst m
      cases h with
      | root => exact LegalGap.root
    · exact close_gap (guarded_open hn h) hw

#print axioms legal_iff_guarded
end BB6.Agent43LagExact
