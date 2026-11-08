import Agent49ParitySource

/-! Exact ternary single-level recurrence and bounded halting language for the
unmodified Cryptids #623 B-drain. Does not decide the blank-root orbit. -/
namespace BB6.Agent49FlatDrainSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource

theorem evalA_second_le (a : Nat) :
    ∀ k m aa bb dd : Nat, evalA a k m = some (aa,bb,dd) → bb ≤ k/3 := by
  induction a with
  | zero =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3=2
    · simp [h2] at h; cases h; omega
    · by_cases h0 : k%3=0
      · simp [h2,h0] at h
      · simp [h2,h0] at h; cases h; omega
  | succ a ih =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3=2
    · simp [h2] at h; cases h; omega
    · by_cases h0 : k%3=0
      · simp [h2,h0] at h; cases h; omega
      · simp [h2,h0] at h
        have hi := ih (k/3) (m+2*(k/3)+3) aa bb dd h
        omega

theorem drain_three (a q d : Nat) (hq : 0<q) :
    drainB a (3*q) d = drainB (a+1) (q-1) (d+6*q+3) := by
  conv => lhs; rw [drainB]
  have hb : 3*q ≠ 0 := by omega
  simp only [if_neg hb]
  have he : evalA a (3*q-1) (d+2*(3*q)+3) = some (a+1,q-1,d+6*q+3) := by
    rw [evalA]
    have hmod : (3*q-1)%3=2 := by omega
    have hdiv : (3*q-1)/3=q-1 := by omega
    simp only [if_pos hmod, hdiv, Option.some.injEq, Prod.mk.injEq, true_and]
    omega
  rw [he]
  simp only [Option.bind_some]
  have hl : q-1<3*q := by omega
  simp only [if_pos hl]

theorem drain_three_one (a q d : Nat) (ha : 0<a) :
    drainB a (3*q+1) d = drainB (a-1) q (d+6*q+7) := by
  conv => lhs; rw [drainB]
  have hb : 3*q+1 ≠ 0 := by omega
  simp only [if_neg hb]
  have he : evalA a (3*q) (d+2*(3*q+1)+3) = some (a-1,q,d+6*q+7) := by
    rw [evalA]
    have hmod2 : (3*q)%3 ≠ 2 := by omega
    have hmod0 : (3*q)%3 = 0 := by omega
    have hapos : a≠0 := by omega
    have hdiv : (3*q)/3=q := by omega
    simp only [if_neg hmod2, if_neg hapos, if_pos hmod0, hdiv, Option.some.injEq, Prod.mk.injEq, true_and]
    omega
  have hm : 3*q+1-1=3*q := by omega
  rw [hm,he]
  simp only [Option.bind_some]
  have hl : q<3*q+1 := by omega
  simp only [if_pos hl]

theorem drain_three_one_zero (q d : Nat) :
    drainB 0 (3*q+1) d = none := by
  conv => lhs; rw [drainB]
  have hb : 3*q+1 ≠ 0 := by omega
  simp only [if_neg hb]
  have he : evalA 0 (3*q) (d+2*(3*q+1)+3) = none := by
    rw [evalA]
    have hm2 : (3*q)%3 ≠ 2 := by omega
    have hm0 : (3*q)%3 = 0 := by omega
    simp [hm2,hm0]
  simp [he]

theorem drain_three_two_zero (q d : Nat) :
    drainB 0 (3*q+2) d = drainB 0 q (d+6*q+7) := by
  conv => lhs; rw [drainB]
  have hb : 3*q+2 ≠ 0 := by omega
  simp only [if_neg hb]
  have he : evalA 0 (3*q+1) (d+2*(3*q+2)+3) = some (0,q,d+6*q+7) := by
    rw [evalA]
    have hm2 : (3*q+1)%3 ≠ 2 := by omega
    have hm0 : (3*q+1)%3 ≠ 0 := by omega
    have hdiv : (3*q+1)/3=q := by omega
    simp [hm2,hm0,hdiv]
    omega
  have hm : 3*q+2-1=3*q+1 := by omega
  rw [hm,he]
  simp only [Option.bind_some]
  have hl : q<3*q+2 := by omega
  simp only [if_pos hl]

theorem drain_three_two (a q d : Nat) (ha : 0<a) :
    drainB a (3*q+2) d = drainB (a-1) (q+1) (d+6*q+5) := by
  conv => lhs; rw [drainB]
  conv => rhs; rw [drainB]
  have hb1 : 3*q+2 ≠ 0 := by omega
  have hb2 : q+1 ≠ 0 := by omega
  simp only [if_neg hb1,if_neg hb2]
  have he : evalA a (3*q+1) (d+2*(3*q+2)+3) =
      evalA (a-1) q (d+6*q+5+2*(q+1)+3) := by
    rw [evalA]
    have h2 : (3*q+1)%3≠2 := by omega
    have h0 : (3*q+1)%3≠0 := by omega
    have hapos : a≠0 := by omega
    have hdiv : (3*q+1)/3=q := by omega
    simp only [if_neg h2,if_neg hapos,if_neg h0, hdiv]
    congr 1 <;> omega
  have hm1 : 3*q+2-1=3*q+1 := by omega
  have hm2 : q+1-1=q := by omega
  rw [hm1,hm2,he]
  cases heval : evalA (a-1) q (d+6*q+5+2*(q+1)+3) with
  | none => simp [heval]
  | some p =>
    rcases p with ⟨aa,bb,dd⟩
    simp only [heval,Option.bind_some]
    have hbound := evalA_second_le (a-1) q (d+6*q+5+2*(q+1)+3) aa bb dd heval
    have hlt1 : bb<3*q+2 := by omega
    have hlt2 : bb<q+1 := by omega
    simp [hlt1,hlt2]

theorem pow_le_ones_succ (a : Nat) : 3^a ≤ ternaryOnes (a+1) := by
  induction a with
  | zero => simp [ternaryOnes]
  | succ a ih =>
    have hp : 3^(a+1)=3*3^a := by rw [Nat.pow_succ]; omega
    simp only [ternaryOnes] at ih ⊢
    omega

def bad : Nat → Nat → Prop
  | 0, b => b=1
  | a+1, b => (b%3=1 ∧ bad a (b/3)) ∨ (b%3=2 ∧ bad a (b/3+1))

theorem drain_none_iff_bad (a : Nat) :
    ∀ b d, b ≤ 3^a → (drainB a b d = none ↔ bad a b) := by
  induction a with
  | zero =>
    intro b d hb
    have hb1 : b≤1 := by simpa using hb
    by_cases hz : b=0
    · subst b; simp [drainB,bad]
    · have hb_one : b=1 := by omega
      subst b
      simpa [bad] using (drain_three_one_zero 0 d)
  | succ a ih =>
    intro b d hb
    let q := b/3
    have hqbound : q ≤ 3^a := by
      dsimp [q]
      have hp : 3^(a+1)=3*3^a := by rw [Nat.pow_succ]; omega
      omega
    have hmod : b%3<3 := Nat.mod_lt _ (by omega)
    have hdiv : b = 3*q+b%3 := by dsimp [q]; omega
    by_cases hr0 : b%3=0
    · have hrep : b=3*q := by omega
      by_cases hq : q=0
      · have hz : b=0 := by omega
        simp [hz,drainB,bad]
      · have hpos : 0<q := by omega
        have hqsmall : q-1 ≤ ternaryOnes (a+2) := by
          have he : 3^(a+1) ≤ ternaryOnes (a+2) := by
            simpa only [Nat.add_assoc, Nat.reduceAdd] using (pow_le_ones_succ (a+1))
          have hp : 3^a≤3^(a+1) := by
            rw [Nat.pow_succ]
            omega
          omega
        obtain ⟨aa,dd,hsafe⟩ := drainB_safe_ones (q-1) (a+2) (d+6*q+3) hqsmall
        rw [hrep,drain_three (a+1) q d hpos,hsafe]
        simp [bad,hr0]
    · by_cases hr1 : b%3=1
      · have hrep : b=3*q+1 := by omega
        have hqsmall : q≤3^a := hqbound
        rw [hrep, drain_three_one (a+1) q d (by omega)]
        have hcode : bad (a+1) (3*q+1) ↔ bad a q := by
          have hmod : (3*q+1)%3=1 := by omega
          have hdiv : (3*q+1)/3=q := by omega
          simp [bad,hmod,hdiv]
        rw [hcode]
        exact ih q (d+6*q+7) hqsmall
      · have hr2 : b%3=2 := by omega
        have hrep : b=3*q+2 := by omega
        have hqsmall : q+1 ≤ 3^a := by
          have hp : 3^(a+1)=3*3^a := by rw [Nat.pow_succ]; omega
          omega
        rw [hrep, drain_three_two (a+1) q d (by omega)]
        have hcode : bad (a+1) (3*q+2) ↔ bad a (q+1) := by
          have hmod : (3*q+2)%3=2 := by omega
          have hdiv : (3*q+2)/3=q := by omega
          simp [bad,hmod,hdiv]
        rw [hcode]
        exact ih (q+1) (d+6*q+5) hqsmall

#print axioms drain_three
#print axioms drain_three_one
#print axioms drain_three_one_zero
#print axioms drain_three_two_zero
#print axioms drain_three_two
#print axioms drain_none_iff_bad
end BB6.Agent49FlatDrainSource
