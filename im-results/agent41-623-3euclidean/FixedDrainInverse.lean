import DrainOrder

namespace BB6.Agent41DrainOrder

/-- Direct flat evaluator, with the six drain recurrence laws exposed. -/
def flat (a b z : Nat) : Option (Nat × Nat) :=
  if b = 0 then some (a,z)
  else if b%3 = 0 then flat (a+1) (b/3-1) (z+6*(b/3)+3)
  else if b%3 = 1 then
    if a=0 then none else flat (a-1) (b/3) (z+6*(b/3)+7)
  else if a=0 then flat 0 (b/3) (z+6*(b/3)+7)
  else flat (a-1) (b/3+1) (z+6*(b/3)+5)
termination_by b
decreasing_by all_goals omega

theorem flat_zero (a z : Nat) : flat a 0 z = some (a,z) := by
  rw [flat]; simp
theorem flat_r0 (a q z : Nat) (hq : 0 < q) :
    flat a (3*q) z = flat (a+1) (q-1) (z+6*q+3) := by
  conv => lhs; rw [flat]
  simp [show 3*q ≠ 0 by omega,show 3*q%3=0 by omega,show 3*q/3=q by omega]
theorem flat_r1 (a q z : Nat) (ha : 0 < a) :
    flat a (3*q+1) z = flat (a-1) q (z+6*q+7) := by
  conv => lhs; rw [flat]
  simp [show 3*q+1 ≠ 0 by omega,show (3*q+1)%3=1 by omega,show (3*q+1)/3=q by omega,show a ≠ 0 by omega]
theorem flat_r10 (q z : Nat) :
    flat 0 (3*q+1) z = none := by
  conv => lhs; rw [flat]
  simp [show 3*q+1 ≠ 0 by omega,show (3*q+1)%3=1 by omega]
theorem flat_r2 (a q z : Nat) (ha : 0 < a) :
    flat a (3*q+2) z = flat (a-1) (q+1) (z+6*q+5) := by
  conv => lhs; rw [flat]
  simp [show 3*q+2 ≠ 0 by omega,show (3*q+2)%3=2 by omega,show (3*q+2)/3=q by omega,show a ≠ 0 by omega]
theorem flat_r20 (q z : Nat) :
    flat 0 (3*q+2) z = flat 0 q (z+6*q+7) := by
  conv => lhs; rw [flat]
  simp [show 3*q+2 ≠ 0 by omega,show (3*q+2)%3=2 by omega,show (3*q+2)/3=q by omega]

theorem flat_laws : FlatLaws flat Prod.mk where
  inj := by intro a z x y h; cases h; exact ⟨rfl,rfl⟩
  zero := flat_zero
  r0 := flat_r0
  r1 := flat_r1
  r10 := flat_r10
  r2 := flat_r2
  r20 := flat_r20

/-- Inverse at a fixed block. The exceptional zero branch is evaluated
directly; at most one recursive inverse call is made per digit. -/
def fixedInverse (b z x y : Nat) : Option Nat :=
  if b=0 then if y=z then some x else none
  else if b%3=0 then
    (fixedInverse (b/3-1) (z+6*(b/3)+3) x y).bind
      (fun a => if a=0 then none else some (a-1))
  else if b%3=1 then
    (fixedInverse (b/3) (z+6*(b/3)+7) x y).map (·+1)
  else if flat 0 (b/3) (z+6*(b/3)+7)=some (x,y) then some 0
  else (fixedInverse (b/3+1) (z+6*(b/3)+5) x y).map (·+1)
termination_by b
decreasing_by all_goals omega

theorem fixedInverse_sound (b : Nat) :
    ∀ z x y a, fixedInverse b z x y = some a → flat a b z = some (x,y) := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro z x y a h
    by_cases hb : b=0
    · subst b
      rw [fixedInverse] at h
      simp at h
      obtain ⟨hy,ha⟩ := h
      subst a; subst y
      exact flat_zero x z
    · let q := b/3
      have hr : b=3*q ∨ b=3*q+1 ∨ b=3*q+2 := by dsimp [q]; omega
      rcases hr with hr|hr|hr
      · have hq : 0 < q := by omega
        rw [fixedInverse] at h
        simp only [if_neg hb,if_pos (show b%3=0 by omega)] at h
        change (fixedInverse (q-1) (z+6*q+3) x y).bind _ = some a at h
        cases he : fixedInverse (q-1) (z+6*q+3) x y with
        | none => simp [he] at h
        | some c =>
          rw [he] at h
          change (if c=0 then none else some (c-1))=some a at h
          by_cases hc : c=0
          · simp [hc] at h
          · simp [hc] at h
            rw [hr,flat_r0 _ _ _ hq,show a+1=c by omega]
            exact ih (q-1) (by omega) _ _ _ _ he
      · rw [fixedInverse] at h
        simp only [if_neg hb,if_neg (show b%3≠0 by omega),if_pos (show b%3=1 by omega)] at h
        change (fixedInverse q (z+6*q+7) x y).map _ = some a at h
        cases he : fixedInverse q (z+6*q+7) x y with
        | none => simp [he] at h
        | some c =>
          simp [he] at h
          rw [hr,flat_r1 _ _ _ (by omega),show a-1=c by omega]
          exact ih q (by omega) _ _ _ _ he
      · rw [fixedInverse] at h
        simp only [if_neg hb,if_neg (show b%3≠0 by omega),if_neg (show b%3≠1 by omega)] at h
        change (if flat 0 q (z+6*q+7)=some (x,y) then some 0
          else (fixedInverse (q+1) (z+6*q+5) x y).map (·+1))=some a at h
        by_cases hzero : flat 0 q (z+6*q+7)=some (x,y)
        · simp [hzero] at h
          subst a
          rw [hr,flat_r20]
          exact hzero
        · simp only [if_neg hzero] at h
          cases he : fixedInverse (q+1) (z+6*q+5) x y with
          | none => simp [he] at h
          | some c =>
            simp [he] at h
            rw [hr,flat_r2 _ _ _ (by omega),show a-1=c by omega]
            exact ih (q+1) (by omega) _ _ _ _ he

theorem fixedInverse_complete (b : Nat) :
    ∀ z x y a, flat a b z = some (x,y) → fixedInverse b z x y = some a := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro z x y a h
    by_cases hb : b=0
    · subst b
      rw [flat_zero] at h
      simp at h
      obtain ⟨ha,hz⟩ := h
      subst a; subst z
      rw [fixedInverse]; simp
    · let q := b/3
      have hr : b=3*q ∨ b=3*q+1 ∨ b=3*q+2 := by dsimp [q]; omega
      rcases hr with hr|hr|hr
      · have hq : 0 < q := by omega
        rw [hr,flat_r0 _ _ _ hq] at h
        have hi := ih (q-1) (by omega) _ _ _ _ h
        rw [fixedInverse]
        simp only [if_neg hb,if_pos (show b%3=0 by omega)]
        change (fixedInverse (q-1) (z+6*q+3) x y).bind _ = some a
        simp [hi]
      · by_cases ha : a=0
        · subst a; rw [hr,flat_r10] at h; contradiction
        · rw [hr,flat_r1 _ _ _ (by omega)] at h
          have hi := ih q (by omega) _ _ _ _ h
          rw [fixedInverse]
          simp only [if_neg hb,if_neg (show b%3≠0 by omega),if_pos (show b%3=1 by omega)]
          change (fixedInverse q (z+6*q+7) x y).map _ = some a
          simp [hi,show a-1+1=a by omega]
      · rw [fixedInverse]
        simp only [if_neg hb,if_neg (show b%3≠0 by omega),if_neg (show b%3≠1 by omega)]
        change (if flat 0 q (z+6*q+7)=some (x,y) then some 0
          else (fixedInverse (q+1) (z+6*q+5) x y).map (·+1))=some a
        by_cases hzero : flat 0 q (z+6*q+7)=some (x,y)
        · have hz : flat 0 b z=some (x,y) := by rw [hr,flat_r20]; exact hzero
          have ha := fixed_block_injective flat Prod.mk flat_laws b 0 a z x y hz h
          simp [hzero,←ha]
        · have ha : a≠0 := by intro he; subst a; rw [hr,flat_r20] at h; contradiction
          rw [hr,flat_r2 _ _ _ (by omega)] at h
          have hi := ih (q+1) (by omega) _ _ _ _ h
          simp [hzero,hi,show a-1+1=a by omega]

theorem fixedInverse_iff (b z x y a : Nat) :
    fixedInverse b z x y=some a ↔ flat a b z=some (x,y) :=
  ⟨fixedInverse_sound b z x y a,fixedInverse_complete b z x y a⟩

#print axioms fixedInverse_iff
end BB6.Agent41DrainOrder
