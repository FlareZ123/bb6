import Std

namespace F118

-- Literal arithmetic definitions from the pinned upstream private PrevState/prevNext.
inductive Src where
  | D (a d c : Nat)
  | K (a k c : Nat)
  deriving DecidableEq, Repr

def srcNext : Src → Option Src
  | .K a k c =>
    if c ≤ k then some (.K a (k-c) (2*c+1)) else some (.D a (2*k+2) (c-k-1))
  | .D (a+1) d 0 => some (.K a (d+1) 0)
  | .D (a+1) d (c+1) =>
    if c ≤ d+1 then some (.K a (d+1-c) (2*c+1))
    else some (.D a (2*d+4) (c-d-2))
  | .D 0 d (c+1) => some (.D (d+1) 0 (c+1))
  | .D 0 _ 0 => none

structure G where
  r : Nat
  n : Nat
  z : Nat
  deriving DecidableEq, Repr

def encode : Src → G
  | .D a d c => ⟨a,d+c+3,c⟩
  | .K a k c => ⟨a+1,k+c+3,c+1⟩

def next (s : G) : Option G :=
  if s.r = 0 then
    if s.z = 0 then none else some ⟨s.n-s.z-2,s.z+3,s.z⟩
  else if s.z = 0 then some ⟨s.r,s.n+1,1⟩
  else if s.n ≤ 2*s.z then some ⟨s.r-1,s.n+1,2*s.z-s.n⟩
  else some ⟨s.r,s.n+1,2*s.z⟩

theorem conjugacy (s : Src) : (srcNext s).map encode = next (encode s) := by
  cases s with
  | K a k c =>
    by_cases h : c ≤ k
    · have h' : ¬ k+c+3 ≤ 2*(c+1) := by omega
      simp [srcNext, encode, next, h, h']
      try (congr 1 <;> omega)
    · have h' : k+c+3 ≤ 2*(c+1) := by omega
      simp [srcNext, encode, next, h, h']
      try (congr 1 <;> omega)
  | D a d c =>
    cases a with
    | zero =>
      cases c with
      | zero => rfl
      | succ c =>
        simp [srcNext, encode, next]
        try (congr 1 <;> omega)
    | succ a =>
      cases c with
      | zero =>
        simp [srcNext, encode, next]
      | succ c =>
        by_cases h : c ≤ d+1
        · have h' : ¬ d+(c+1)+3 ≤ 2*(c+1) := by omega
          simp [srcNext, encode, next, h, h']
          try (congr 1 <;> omega)
        · have h' : d+(c+1)+3 ≤ 2*(c+1) := by omega
          simp [srcNext, encode, next, h, h']
          try (congr 1 <;> omega)

def iterate {α : Type} (f : α → Option α) : Nat → α → Option α
  | 0, s => some s
  | t+1, s => (f s).bind (iterate f t)

theorem iterate_conjugacy (t : Nat) (s : Src) :
    (iterate srcNext t s).map encode = iterate next t (encode s) := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    simp only [iterate, ← conjugacy]
    cases h : srcNext s with
    | none => rfl
    | some s' => exact ih s'

theorem halt_iff (s : Src) : (∃ t, iterate srcNext t s = none) ↔
    (∃ t, iterate next t (encode s) = none) := by
  constructor
  · rintro ⟨t,h⟩
    exact ⟨t, by rw [← iterate_conjugacy, h]; rfl⟩
  · rintro ⟨t,h⟩
    refine ⟨t, ?_⟩
    rw [← iterate_conjugacy] at h
    cases h' : iterate srcNext t s <;> simp_all

theorem root_halt_iff : (∃ t, iterate srcNext t (.D 0 0 1) = none) ↔
    (∃ t, iterate next t ⟨0,4,1⟩ = none) := halt_iff _

def valid (s : G) : Prop := 3 ≤ s.n ∧ s.z+2 ≤ s.n ∧ (s.r=0 ∨ s.z=0 → s.z+3 ≤ s.n)

theorem encode_valid (s : Src) : valid (encode s) := by
  cases s <;> simp [encode,valid] <;> omega

theorem next_valid (s s' : G) (h : valid s) (hs : next s = some s') : valid s' := by
  rcases s with ⟨r,n,z⟩
  simp only [valid] at h
  simp only [next] at hs
  split at hs
  · split at hs
    · contradiction
    · simp only [Option.some.injEq] at hs
      subst s'; simp [valid]
  · split at hs
    · simp only [Option.some.injEq] at hs
      subst s'; simp [valid]; omega
    · split at hs
      · simp only [Option.some.injEq] at hs
        subst s'; simp [valid]; omega
      · simp only [Option.some.injEq] at hs
        subst s'; simp [valid]; omega

theorem active_greedy (r n z : Nat) (hr : 0 < r) (_hn : 3 ≤ n) (hz : 0 < z) (hzn : z+2 ≤ n) :
    next ⟨r,n,z⟩ = some ⟨r-(2*z/n),n+1,2*z%n⟩ := by
  have h2 : 2*z < 2*n := by omega
  by_cases h : n ≤ 2*z
  · have hd : 2*z/n=1 := by
      apply Nat.div_eq_of_lt_le (k := 1) <;> omega
    have hm := Nat.mod_add_div (2*z) n
    rw [hd] at hm
    simp [next, (Nat.ne_of_gt hr), (Nat.ne_of_gt hz), h, hd]
    try (congr 1 <;> omega)
  · have hd : 2*z/n=0 := Nat.div_eq_of_lt (by omega)
    have hm : 2*z%n=2*z := Nat.mod_eq_of_lt (by omega)
    simp [next, (Nat.ne_of_gt hr), (Nat.ne_of_gt hz), h, hd, hm]

#print axioms conjugacy
#print axioms root_halt_iff
#print axioms next_valid
#print axioms active_greedy

-- The finite countdown drain is total independently of greedy termination.
def drain (r n z : Nat) : Nat × Nat :=
  if r = 0 then (n,z)
  else if z = 0 then drain r (n+1) 1
  else if n ≤ 2*z then drain (r-1) (n+1) (2*z-n)
  else drain r (n+1) (2*z)
termination_by (r,n+1-2*z)
decreasing_by
  all_goals first | (apply Prod.Lex.left; omega) | (apply Prod.Lex.right; omega)

def out (s : G) : Nat × Nat := drain s.r s.n s.z

theorem drain_step (s s' : G) (hr : s.r ≠ 0) (h : next s = some s') : out s = out s' := by
  rcases s with ⟨r,n,z⟩
  simp [next,hr] at h
  rw [out, drain.eq_def]
  simp only [hr,ite_false]
  split at h
  · rename_i hz
    simp [hz] at ⊢
    simp only [Option.some.injEq] at h
    subst s'; rfl
  · rename_i hz
    simp only [hz,ite_false]
    split at h
    · rename_i hw
      simp only [hw,ite_true]
      simp only [Option.some.injEq] at h
      subst s'; rfl
    · rename_i hw
      simp only [hw,ite_false]
      simp only [Option.some.injEq] at h
      subst s'; rfl

theorem source_step_drain (s s' : Src) (hr : (encode s).r ≠ 0) (h : srcNext s = some s') :
    out (encode s) = out (encode s') := by
  apply drain_step _ _ hr
  rw [← conjugacy,h]; rfl

-- Literal public upstream high-level arithmetic definitions, with the section state
-- represented as a pair rather than its single-constructor inductive type.
def evalK (k c : Nat) : Nat × Nat :=
  let c1 := max c 1
  if c1 ≤ k then evalK (k-c1) (2*c1+1)
  else (2*k+2,c1-k-1)
termination_by k
decreasing_by omega

def drainD (a d c : Nat) : Option (Nat × Nat) :=
  if a=0 then
    if c=0 then none else some (d+1,c)
  else
    let nextDC :=
      if c=0 then evalK (d+1) 0
      else if c-1 ≤ d+1 then evalK (d+1-(c-1)) (2*(c-1)+1)
      else (2*d+4,c-1-d-2)
    drainD (a-1) nextDC.1 nextDC.2
termination_by a
decreasing_by omega

theorem evalK_drain_pos (a k c : Nat) (hc : c ≠ 0) :
    out (encode (.K a k c)) = out (encode (.D a (evalK k c).1 (evalK k c).2)) := by
  rw [evalK.eq_def, show max c 1=c by omega]
  by_cases h : c ≤ k
  · simp only [h,ite_true]
    have hs : srcNext (.K a k c) = some (.K a (k-c) (2*c+1)) := by simp [srcNext,h]
    rw [source_step_drain _ _ (by simp [encode]) hs]
    exact evalK_drain_pos a (k-c) (2*c+1) (by omega)
  · simp only [h,ite_false]
    apply source_step_drain
    · simp [encode]
    · simp [srcNext,h]
termination_by k
decreasing_by omega

theorem evalK_drain (a k c : Nat) :
    out (encode (.K a k c)) = out (encode (.D a (evalK k c).1 (evalK k c).2)) := by
  by_cases h : c=0
  · subst c
    have hs : srcNext (.K a k 0) = some (.K a k 1) := by simp [srcNext]
    rw [source_step_drain _ _ (by simp [encode]) hs]
    have he : evalK k 0 = evalK k 1 := by rw [evalK.eq_def,evalK.eq_def]; simp
    rw [he]
    exact evalK_drain_pos a k 1 (by decide)
  · exact evalK_drain_pos a k c h

def finish (p : Nat × Nat) : Option (Nat × Nat) :=
  if p.2=0 then none else some (p.1-p.2-2,p.2)

theorem exact_drainD (a d c : Nat) : drainD a d c = finish (out (encode (.D a d c))) := by
  cases a with
  | zero =>
    rw [drainD.eq_def]
    simp only [out,encode]
    rw [drain.eq_def]
    simp only [finish]
    cases c <;> simp <;> try omega
  | succ a =>
    rw [drainD.eq_def]
    simp only [Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel]
    cases c with
    | zero =>
      have h : srcNext (.D (a+1) d 0) = some (.K a (d+1) 0) := rfl
      rw [source_step_drain _ _ (by simp [encode]) h,evalK_drain]
      exact exact_drainD a _ _
    | succ c =>
      simp only [Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel]
      by_cases h : c ≤ d+1
      · simp only [h,ite_true]
        have hs : srcNext (.D (a+1) d (c+1)) = some (.K a (d+1-c) (2*c+1)) := by simp [srcNext,h]
        rw [source_step_drain _ _ (by simp [encode]) hs,evalK_drain]
        exact exact_drainD a _ _
      · simp only [h,ite_false]
        have hs : srcNext (.D (a+1) d (c+1)) = some (.D a (2*d+4) (c-d-2)) := by simp [srcNext,h]
        rw [source_step_drain _ _ (by simp [encode]) hs]
        exact exact_drainD a _ _
termination_by a

def sectionNext (p : Nat × Nat) : Option (Nat × Nat) :=
  finish (drain p.1 (p.2+3) p.2)

theorem section_eq (a c : Nat) : drainD a 0 c = sectionNext (a,c) := by
  rw [exact_drainD]; simp [out,encode,sectionNext]

#print axioms drain_step
#print axioms exact_drainD
#print axioms section_eq
end F118
