import Lean

/-! Three-register MSB ternary fold for the full #623 fatal spectrum.
    The recurrence hypothesis is exactly Agent49FullSpectrum.badAll's equation.
    This arithmetic module requires no Mathlib or original-machine imports. -/
namespace BB6.Agent41SpectrumRegisters

structure Masks where
  lo : Nat
  mid : Nat
  hi : Nat
  deriving DecidableEq, Repr

def seed : Masks := ⟨0,0,1⟩

def step (s : Masks) (r : Nat) : Masks :=
  let a := s.lo
  let b := s.mid
  let c := s.hi
  if r = 0 then ⟨2*b+a%2,a/2,2*b+1⟩
  else if r = 1 then ⟨a/2,2*b+1,2*c+b%2⟩
  else ⟨2*b+1,2*c+b%2,b/2⟩

def masks (b : Nat) : Masks :=
  if b = 0 then seed else step (masks (b/3)) (b%3)
termination_by b
decreasing_by omega

/-- Exact source-shaped Boolean recurrence; the parameterization allows a
source adapter without copying any upstream drain definitions. -/
def Recurrence (bad : Nat → Nat → Bool) : Prop :=
  ∀ a b, bad a b =
    (if b=0 then false
     else if b%3=0 then bad (a+1) (b/3-1)
     else if b%3=1 then if a=0 then true else bad (a-1) (b/3)
     else if a=0 then bad 0 (b/3) else bad (a-1) (b/3+1))

def Encodes (bad : Nat → Nat → Bool) (s : Masks) (b : Nat) : Prop :=
  ∀ a, s.lo.testBit a = bad a (b-1) ∧
       s.mid.testBit a = bad a b ∧ s.hi.testBit a = bad a (b+1)

private theorem up_zero (x y : Nat) (hy : y < 2) :
    (2*x+y).testBit 0 = decide (y=1) := by
  simp only [Nat.testBit_zero]
  have h : (2*x+y)%2 = y := by omega
  rw [h]

private theorem up_succ (x y a : Nat) (hy : y < 2) :
    (2*x+y).testBit (a+1) = x.testBit a := by
  rw [Nat.testBit_add_one]
  have h : (2*x+y)/2 = x := by omega
  rw [h]

private theorem zero_bad (bad : Nat → Nat → Bool) (h : Recurrence bad) (a : Nat) :
    bad a 0 = false := by rw [h]; simp

private theorem encode_zero (bad : Nat → Nat → Bool) (h : Recurrence bad) :
    Encodes bad seed 0 := by
  intro a
  have hz := zero_bad bad h a
  rw [show (0:Nat)-1=0 by decide, hz]
  simp only [seed, Nat.zero_testBit, true_and]
  rw [h a 1]
  cases a <;> simp [zero_bad bad h, Nat.testBit_succ]

private theorem encode_step (bad : Nat → Nat → Bool) (h : Recurrence bad)
    (s : Masks) (q r : Nat) (hr : r<3) (hs : Encodes bad s q) :
    Encodes bad (step s r) (3*q+r) := by
  have hz := zero_bad bad h
  have hb : ∀ x, x%2 < 2 := fun x => Nat.mod_lt _ (by decide)
  have hp : ∀ x, decide (x%2=1) = x.testBit 0 := fun x => (Nat.testBit_zero x).symm
  have hlo : ∀ a, s.lo.testBit a = bad a (q-1) := fun a => (hs a).1
  have hmid : ∀ a, s.mid.testBit a = bad a q := fun a => (hs a).2.1
  have hhi : ∀ a, s.hi.testBit a = bad a (q+1) := fun a => (hs a).2.2
  have e0 : ∀ a, (s.lo/2).testBit a = bad a (3*q) := by
    intro a
    rw [Nat.testBit_div_two, hlo]
    by_cases hq : q=0
    · simp [hq, hz]
    · rw [h a (3*q)]
      have hn : 3*q ≠ 0 := by omega
      have hm : (3*q)%3=0 := by omega
      have hd : (3*q)/3=q := by omega
      simp only [if_neg hn, hm, if_true, hd]
  have e1 : ∀ a, (2*s.mid+1).testBit a = bad a (3*q+1) := by
    intro a
    rw [h a (3*q+1)]
    have hn : 3*q+1 ≠ 0 := by omega
    have hm : (3*q+1)%3=1 := by omega
    have hd : (3*q+1)/3=q := by omega
    simp only [if_neg hn, hm, hd, Nat.one_ne_zero, if_false, if_true]
    cases a with
    | zero => rw [up_zero _ _ (by decide)]; simp
    | succ a => rw [up_succ _ _ _ (by decide), hmid]; simp
  have e2 : ∀ a, (2*s.hi+s.mid%2).testBit a = bad a (3*q+2) := by
    intro a
    rw [h a (3*q+2)]
    have hn : 3*q+2 ≠ 0 := by omega
    have hm : (3*q+2)%3=2 := by omega
    have hd : (3*q+2)/3=q := by omega
    simp only [if_neg hn, hm, hd, show (2:Nat)≠0 by decide, show (2:Nat)≠1 by decide, if_false]
    cases a with
    | zero => rw [up_zero _ _ (hb _), hp, hmid]; simp
    | succ a => rw [up_succ _ _ _ (hb _), hhi]; simp
  have em : ∀ a, (2*s.mid+s.lo%2).testBit a = bad a (3*q-1) := by
    intro a
    by_cases hq : q=0
    · cases a with
      | zero => rw [up_zero _ _ (hb _), hp, hlo]; simp [hq, hz]
      | succ a => rw [up_succ _ _ _ (hb _), hmid]; simp [hq, hz]
    · rw [h a (3*q-1)]
      have hn : 3*q-1 ≠ 0 := by omega
      have hm : (3*q-1)%3=2 := by omega
      have hd : (3*q-1)/3=q-1 := by omega
      simp only [if_neg hn, hm, hd, show (2:Nat)≠0 by decide, show (2:Nat)≠1 by decide, if_false]
      cases a with
      | zero => rw [up_zero _ _ (hb _), hp, hlo]; simp
      | succ a =>
        rw [up_succ _ _ _ (hb _), hmid]
        have he : q-1+1=q := by omega
        simp [he]
  have ep : ∀ a, (s.mid/2).testBit a = bad a (3*q+3) := by
    intro a
    rw [Nat.testBit_div_two, hmid, h a (3*q+3)]
    have hn : 3*q+3 ≠ 0 := by omega
    have hm : (3*q+3)%3=0 := by omega
    have hd : (3*q+3)/3-1=q := by omega
    simp [hn, hm, hd]
  intro a
  have rr : r=0 ∨ r=1 ∨ r=2 := by omega
  rcases rr with rfl|rfl|rfl
  · simp only [step, if_true, Nat.add_zero]
    exact ⟨em a,e0 a,e1 a⟩
  · simp only [step, Nat.one_ne_zero, if_false, if_true]
    have he : 3*q+1-1=3*q := by omega
    rw [he]
    exact ⟨e0 a,e1 a,e2 a⟩
  · simp only [step, show (2:Nat)≠0 by decide, show (2:Nat)≠1 by decide, if_false]
    have he : 3*q+2-1=3*q+1 := by omega
    rw [he]
    exact ⟨e1 a,e2 a,ep a⟩

/-- Every bit in each register is exact, at every block count. -/
theorem masks_correct (bad : Nat → Nat → Bool) (h : Recurrence bad) (b : Nat) :
    Encodes bad (masks b) b := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    rw [masks]
    by_cases hb : b=0
    · simpa [hb] using encode_zero bad h
    · simp only [if_neg hb]
      have hq : b/3 < b := by omega
      have he : 3*(b/3)+b%3=b := by omega
      simpa only [he] using encode_step bad h (masks (b/3)) (b/3) (b%3)
        (Nat.mod_lt _ (by decide)) (ih _ hq)

/-- An online ternary fold: append one digit to the represented block count. -/
theorem masks_append (b r : Nat) (hr : r<3) :
    masks (3*b+r) = step (masks b) r := by
  rw [masks]
  by_cases hz : 3*b+r=0
  · have hb : b=0 := by omega
    have h0 : r=0 := by omega
    subst b; subst r
    have hs : masks 0 = seed := by rw [masks]; rfl
    simp [hs, step, seed]
  · have hd : (3*b+r)/3=b := by omega
    have hm : (3*b+r)%3=r := by omega
    simp only [if_neg hz, hd, hm]

#print axioms masks_correct
#print axioms masks_append
end BB6.Agent41SpectrumRegisters
