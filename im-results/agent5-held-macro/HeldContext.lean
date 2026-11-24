import HeldStrong
set_option maxHeartbeats 0
namespace HeldMacro
open Q

namespace GoodL

theorem mod4_zero {n : Nat} (h : GoodL n) (h4 : n%4=0) : n=0 ∨ n%8=4 := by
  cases h with
  | blank => exact Or.inl rfl
  | @one n h => omega
  | @zero n h hm _ => omega

theorem mod8_one {n : Nat} (h : GoodL n) (h8 : n%8=1) : n=1 ∨ n%16=9 := by
  cases h with
  | blank => omega
  | @zero n h _ _ => omega
  | @one n h =>
    have h4 : n%4=0 := by omega
    rcases h.mod4_zero h4 with h0|h4 <;> omega

theorem zero_pop_one {n : Nat} (h : GoodL n) (hb : n%2=0) (h8 : (n/2)%8=1) : n/2=1 := by
  cases h with
  | blank => omega
  | @one n h => omega
  | @zero n h _ h16 =>
    have h8' : n%8=1 := by omega
    rcases h.mod8_one h8' with hh|hh <;> omega
end GoodL

def aCtx (l r : Nat) : Prop :=
  (l=0 ∧ r=0) ∨ (l=2 ∧ r%4=0) ∨ (l%8=6 ∧ r%4=0) ∨ l%16=9 ∨
  (r%16=10 ∧ (l=0 ∨ l%2=1)) ∨ (r%16=11 ∧ (l=0 ∨ l%4≠0))

def bCtx (l r : Nat) : Prop := r%16=2 → l=0

def dCtx (l r : Nat) : Prop := r%2=0 → l%8=1 → l=1

def headCtx (c : Config) : Prop :=
  match c.q with
  | A => aCtx c.l c.r
  | B => bCtx c.l c.r
  | D => dCtx c.l c.r
  | _ => True

def div4R (d : SConfig) : Bool := d.r.coeff%4==0 && d.r.off%4==0

def aShape (q : Q) (b a : Nat) (d : SConfig) : Bool :=
  (d.l.coeff%16==0 && d.l.off%16==9) ||
  (d.l.coeff%8==0 && d.l.off%8==6 && div4R d) ||
  (q==B && a%16==2 && d.l==⟨8,4*b+2⟩ && div4R d) ||
  (q==D && a%2==0 && d.l==⟨1,0⟩ && d.r.coeff%16==0 && d.r.off%16==b+10)

def bShape (q : Q) (b a : Nat) (d : SConfig) : Bool :=
  d.r.coeff%16==0 && (d.r.off%16!=2 || (q==A && a%4==2 && b==0 && d.l==⟨1,0⟩))

def dShape (b : Nat) (d : SConfig) : Bool :=
  d.l==⟨1,0⟩ && d.r.coeff%2==0 && d.r.off%2==b

def checkCtx (q : Q) (b a : Nat) : Bool :=
  match symbolic q b a with
  | .stop _ _ => true
  | .next _ d => match d.q with
    | A => aShape q b a d
    | B => bShape q b a d
    | D => dShape b d
    | _ => false

theorem finite_ctx (q : Q) (b : Fin 2) (a : Fin 32) (hq : boundaryQ q = true)
    (hr : strongR q a.val = true) : checkCtx q b.val a.val = true := by
  have hA : ∀ (b : Fin 2) (a : Fin 32), strongR A a.val = true → checkCtx A b.val a.val = true := by decide
  have hB : ∀ (b : Fin 2) (a : Fin 32), strongR B a.val = true → checkCtx B b.val a.val = true := by decide
  have hD : ∀ (b : Fin 2) (a : Fin 32), strongR D a.val = true → checkCtx D b.val a.val = true := by decide
  cases q with
  | A => exact hA b a hr
  | B => exact hB b a hr
  | D => exact hD b a hr
  | C | E | F => simp [boundaryQ] at hq

theorem aCtx_01 {l r : Nat} (h : aCtx l r) (hr : r%4=2) : l=0 ∨ l%2=1 := by
  unfold aCtx at h
  rcases h with h|h|h|h|h|h <;> omega

theorem affine_mod (e : Affine) (u m : Nat) (hm : e.coeff%m=0) : e.eval u%m=e.off%m := by
  simp only [Affine.eval, Nat.add_mod, Nat.mul_mod, hm, Nat.zero_mul, Nat.zero_mod, Nat.zero_add, Nat.mod_mod]

theorem ctx_preserved (c d : Config) (k : Nat) (hb : boundaryQ c.q = true)
    (ha : advance c = .next k d) (hl : GoodL c.l) (hr : strongR c.q c.r = true)
    (hg : leftGuard c) (hc : headCtx c) : headCtx d := by
  let b : Fin 2 := ⟨c.l%2,by omega⟩
  let a : Fin 32 := ⟨c.r%32,by omega⟩
  have hr' : strongR c.q a.val = true := by simpa [a,strongR_mod] using hr
  have H := finite_ctx c.q b a hb hr'
  change (symbolic c.q b.val a.val).eval (c.l/2) (c.r/32) = .next k d at ha
  unfold checkCtx at H
  cases he : symbolic c.q b.val a.val with
  | stop n e => rw [he] at ha; simp [SResult.eval] at ha
  | next n e =>
    rw [he] at H ha
    simp [SResult.eval] at ha
    obtain ⟨_,hd⟩ := ha
    rw [←hd]
    simp only [headCtx,SConfig.eval]
    cases hq : e.q <;> simp only [hq] at H ⊢
    case A =>
      simp only [aShape,div4R,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,or_assoc,and_assoc] at H
      rcases H with H|H|H|H
      · exact Or.inr (Or.inr (Or.inr (Or.inl ((affine_mod e.l (c.l/2) 16 H.1).trans H.2))))
      · exact Or.inr (Or.inr (Or.inl ⟨(affine_mod e.l (c.l/2) 8 H.1).trans H.2.1,(affine_mod e.r (c.r/32) 4 H.2.2.1).trans H.2.2.2⟩))
      · obtain ⟨hB,ha16,hlsh,hrm,hro⟩ := H
        have hr16 : c.r%16=2 := by simp [a] at ha16; omega
        have hcB : bCtx c.l c.r := by simpa [headCtx,hB] using hc
        have h0 := hcB hr16
        have hb0 : b.val=0 := by simp [b,h0]
        refine Or.inr (Or.inl ⟨?_,(affine_mod e.r (c.r/32) 4 hrm).trans hro⟩)
        simp [hlsh,Affine.eval,h0,hb0]
      · obtain ⟨hD,ha0,hlsh,hrm,hro⟩ := H
        have hr0 : c.r%2=0 := by simp [a] at ha0; omega
        have hr16 := (affine_mod e.r (c.r/32) 16 hrm).trans hro
        have hg' := hg (Or.inr hD) hr0
        have hcD : dCtx c.l c.r := by simpa [headCtx,hD] using hc
        have hlv : e.l.eval (c.l/2)=c.l/2 := by simp [hlsh,Affine.eval]
        rw [hlv]
        by_cases hbit : b.val=0
        · have h0 : c.l%2=0 := by simpa [b] using hbit
          have hl' : c.l/2=0 ∨ (c.l/2)%2=1 := by
            by_cases h4 : c.l%4=0
            · rcases hl.mod4_zero h4 with h0'|h8 <;> omega
            · omega
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,hl'⟩))))
        · have hbit' : b.val=1 := by have := b.isLt; omega
          have h1 : c.l%2=1 := by simpa [b] using hbit'
          have hl' : c.l/2=0 ∨ (c.l/2)%4≠0 := by
            by_cases h4 : (c.l/2)%4=0
            · have h8 : c.l%8=1 := by omega
              have heq := hcD hr0 h8
              omega
            · exact Or.inr h4
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,hl'⟩))))
    case B =>
      simp only [bShape,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,bne_iff_ne,and_assoc] at H
      unfold bCtx
      intro h2
      have h2' : e.r.off%16=2 := (affine_mod e.r (c.r/32) 16 H.1).symm.trans h2
      rcases H.2 with H|H
      · contradiction
      · obtain ⟨hA,ha2,hb0,hlsh⟩ := H
        have ha2' : c.r%4=2 := by simp [a] at ha2; omega
        have hcA : aCtx c.l c.r := by simpa [headCtx,hA] using hc
        have h0 := aCtx_01 hcA ha2'
        have hl0 : c.l=0 := by simp [b] at hb0; omega
        simp [hlsh,Affine.eval,hl0]
    case D =>
      simp only [dShape,Bool.and_eq_true,beq_iff_eq,and_assoc] at H
      unfold dCtx
      intro hr0 h8
      have hbit := (affine_mod e.r (c.r/32) 2 H.2.1).trans H.2.2
      have hlv : e.l.eval (c.l/2)=c.l/2 := by simp [H.1,Affine.eval]
      rw [hlv] at h8 ⊢
      have hb0 : c.l%2=0 := by simp [b] at hbit; omega
      exact hl.zero_pop_one hb0 h8
    all_goals trivial

theorem macroReach_context {c : Config} (h : MacroReach c) : headCtx c := by
  induction h with
  | blank => exact Or.inl ⟨rfl,rfl⟩
  | @next c d k h ha ih =>
    obtain ⟨hb,hl,hr,hg⟩ := macroReach_strong h
    exact ctx_preserved c d k hb ha hl hr hg ih

#print axioms ctx_preserved
#print axioms macroReach_context
end HeldMacro
