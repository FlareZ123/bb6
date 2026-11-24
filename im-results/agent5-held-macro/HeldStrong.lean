import HeldMacro
set_option maxHeartbeats 0
namespace HeldMacro
open Q

/-- Far-to-near left words admit 1 freely, and 0 unless it would create
    three trailing zeroes or the factor 10010. Leading zeroes are blank. -/
inductive GoodL : Nat → Prop where
  | blank : GoodL 0
  | one {n} : GoodL n → GoodL (2*n+1)
  | zero {n} : GoodL n → n%4 ≠ 0 → n%16 ≠ 9 → GoodL (2*n)

namespace GoodL

theorem pop {n : Nat} (h : GoodL n) : GoodL (n/2) := by
  cases h with
  | blank => exact .blank
  | @one n h => simpa [show (2*n+1)/2=n by omega] using h
  | @zero n h h4 h16 => simpa [show (2*n)/2=n by omega] using h

theorem zero_pop {n : Nat} (h : GoodL n) (hb : n%2=0) : (n/2)%8 ≠ 4 := by
  cases h with
  | blank => decide
  | @one n h => omega
  | @zero n h h4 h16 => omega

theorem push110 {n : Nat} (h : GoodL n) : GoodL (8*n+6) := by
  have h1 := GoodL.one (GoodL.one h)
  have h2 := GoodL.zero h1 (by omega) (by omega)
  rwa [show 2*(2*(2*n+1)+1)=8*n+6 by omega] at h2

theorem push11001 {n : Nat} (h : GoodL n) : GoodL (32*n+25) := by
  have h1 := GoodL.push110 h
  have h2 := GoodL.zero h1 (by omega) (by omega)
  have h3 := GoodL.one h2
  rwa [show 2*(2*(8*n+6))+1=32*n+25 by omega] at h3

theorem push10 {n : Nat} (h : GoodL n) (h8 : n%8 ≠ 4) : GoodL (4*n+2) := by
  have h1 := GoodL.one h
  have h2 := GoodL.zero h1 (by omega) (by omega)
  rwa [show 2*(2*n+1)=4*n+2 by omega] at h2

theorem push1001 {n : Nat} (h : GoodL n) (h8 : n%8 ≠ 4) : GoodL (16*n+9) := by
  have h1 := GoodL.push10 h h8
  have h2 := GoodL.zero h1 (by omega) (by omega)
  have h3 := GoodL.one h2
  rwa [show 2*(2*(4*n+2))+1=16*n+9 by omega] at h3
end GoodL

def strongR (q : Q) (r : Nat) : Bool :=
  if q=B then r%8==2 || r%8==3 else if q=D then r%8==4 || r%8==5 else true

def leftGuard (c : Config) : Prop :=
  (c.q=B ∨ c.q=D) → c.r%2=0 → c.l%8 ≠ 4

def strongLeftShape (q : Q) (b a : Nat) (d : SConfig) : Bool :=
  d.l == ⟨1,0⟩ || d.l == ⟨16,8*b+6⟩ || d.l == ⟨64,32*b+25⟩ ||
  ((q==B && a%2==0) && (d.l==⟨8,4*b+2⟩ || d.l==⟨32,16*b+9⟩))

def strongRightShape (b : Nat) (d : SConfig) : Bool :=
  (d.q != B && d.q != D) ||
  (d.l == ⟨1,0⟩ && d.r.coeff%8==0 && strongR d.q d.r.off && d.r.off%2==b)

def checkStrong (q : Q) (b a : Nat) : Bool :=
  match symbolic q b a with
  | .next _ d => strongLeftShape q b a d && strongRightShape b d
  | .stop _ _ => q==A

theorem finite_strong (q : Q) (b : Fin 2) (a : Fin 32) (hq : boundaryQ q = true)
    (hr : strongR q a.val = true) : checkStrong q b.val a.val = true := by
  have hA : ∀ (b : Fin 2) (a : Fin 32), strongR A a.val = true → checkStrong A b.val a.val = true := by decide
  have hB : ∀ (b : Fin 2) (a : Fin 32), strongR B a.val = true → checkStrong B b.val a.val = true := by decide
  have hD : ∀ (b : Fin 2) (a : Fin 32), strongR D a.val = true → checkStrong D b.val a.val = true := by decide
  cases q with
  | A => exact hA b a hr
  | B => exact hB b a hr
  | D => exact hD b a hr
  | C | E | F => simp [boundaryQ] at hq

theorem strongR_mod (q : Q) (r : Nat) : strongR q (r%32) = strongR q r := by
  have hm : r%32%8=r%8 := by omega
  simp [strongR,hm]

theorem strong_preserved (c d : Config) (k : Nat) (hb : boundaryQ c.q = true)
    (ha : advance c = .next k d) (hl : GoodL c.l) (hr : strongR c.q c.r = true)
    (hg : leftGuard c) : GoodL d.l ∧ strongR d.q d.r = true ∧ leftGuard d := by
  let b : Fin 2 := ⟨c.l%2,by omega⟩
  let a : Fin 32 := ⟨c.r%32,by omega⟩
  have hr' : strongR c.q a.val = true := by simpa [a,strongR_mod] using hr
  have H := finite_strong c.q b a hb hr'
  change (symbolic c.q b.val a.val).eval (c.l/2) (c.r/32) = .next k d at ha
  unfold checkStrong at H
  cases he : symbolic c.q b.val a.val with
  | stop n e => rw [he] at ha; simp [SResult.eval] at ha
  | next n e =>
    rw [he] at H
    change (strongLeftShape c.q b.val a.val e && strongRightShape b.val e) = true at H
    simp only [Bool.and_eq_true] at H
    rw [he] at ha
    simp [SResult.eval] at ha
    obtain ⟨_,hd⟩ := ha
    rw [←hd]
    simp only [SConfig.eval]
    constructor
    · have HL := H.1
      simp only [strongLeftShape,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,or_assoc] at HL
      rcases HL with HL|HL|HL|HL
      · rw [HL]; simpa [Affine.eval] using hl.pop
      · rw [HL]; simp only [Affine.eval]
        have heq : 16*(c.l/2)+(8*b.val+6) = 8*c.l+6 := by simp [b]; omega
        rw [heq]; exact hl.push110
      · rw [HL]; simp only [Affine.eval]
        have heq : 64*(c.l/2)+(32*b.val+25) = 32*c.l+25 := by simp [b]; omega
        rw [heq]; exact hl.push11001
      · obtain ⟨⟨hq,ha0⟩,hlsh⟩ := HL
        have hr0 : c.r%2=0 := by simp [a] at ha0; omega
        have h8 := hg (Or.inl hq) hr0
        rcases hlsh with HL|HL
        · rw [HL]; simp only [Affine.eval]
          have heq : 8*(c.l/2)+(4*b.val+2) = 4*c.l+2 := by simp [b]; omega
          rw [heq]; exact hl.push10 h8
        · rw [HL]; simp only [Affine.eval]
          have heq : 32*(c.l/2)+(16*b.val+9) = 16*c.l+9 := by simp [b]; omega
          rw [heq]; exact hl.push1001 h8
    · have HR := H.2
      simp only [strongRightShape,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne] at HR
      rcases HR with HR|HR
      · constructor
        · simp [strongR,HR.1,HR.2]
        · unfold leftGuard; simp [HR.1,HR.2]
      · obtain ⟨⟨⟨hlsh,hcoeff⟩,hrs⟩,hbit⟩ := HR
        have hm8 : e.r.eval (c.r/32)%8=e.r.off%8 := by
          unfold Affine.eval
          have hh : e.r.coeff=8*(e.r.coeff/8) := by omega
          rw [hh,Nat.mul_assoc,Nat.mul_add_mod]
        have hm2 : e.r.eval (c.r/32)%2=e.r.off%2 := by omega
        constructor
        · unfold strongR at hrs ⊢
          rw [hm8]; exact hrs
        · unfold leftGuard
          simp only
          intro _ h0
          have h0' : c.l%2=0 := by simp [b] at hbit; omega
          rw [hlsh]; simpa [Affine.eval] using hl.zero_pop h0'

theorem stop_only_A (c d : Config) (k : Nat) (hb : boundaryQ c.q = true)
    (hr : strongR c.q c.r = true) (ha : advance c = .stop k d) : c.q=A := by
  let b : Fin 2 := ⟨c.l%2,by omega⟩
  let a : Fin 32 := ⟨c.r%32,by omega⟩
  have hr' : strongR c.q a.val = true := by simpa [a,strongR_mod] using hr
  have H := finite_strong c.q b a hb hr'
  change (symbolic c.q b.val a.val).eval (c.l/2) (c.r/32) = .stop k d at ha
  unfold checkStrong at H
  cases he : symbolic c.q b.val a.val with
  | next n e => rw [he] at ha; simp [SResult.eval] at ha
  | stop n e => rw [he] at H; simpa using H

inductive MacroReach : Config → Prop where
  | blank : MacroReach ⟨A,0,0⟩
  | next {c d : Config} {k : Nat} : MacroReach c → advance c = .next k d → MacroReach d

theorem macroReach_strong {c : Config} (h : MacroReach c) :
    boundaryQ c.q = true ∧ GoodL c.l ∧ strongR c.q c.r = true ∧ leftGuard c := by
  induction h with
  | blank => exact ⟨rfl,.blank,rfl,by simp [leftGuard]⟩
  | @next c d k h ha ih =>
    have hc := correct c ih.1
    rw [ha] at hc
    exact ⟨hc.2.2,strong_preserved c d k ih.1 ha ih.2.1 ih.2.2.1 ih.2.2.2⟩

theorem macroReach_stop_A {c d : Config} {k : Nat} (h : MacroReach c) (ha : advance c = .stop k d) : c.q=A :=
  stop_only_A c d k (macroReach_strong h).1 (macroReach_strong h).2.2.1 ha

#print axioms strong_preserved
#print axioms macroReach_strong
#print axioms macroReach_stop_A
end HeldMacro
