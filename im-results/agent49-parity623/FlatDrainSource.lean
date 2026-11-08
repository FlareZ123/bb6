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
    have hle1 : bb ≤ 3*q+1 := by omega
    have hle2 : bb ≤ q := by omega
    simp [hle1,hle2]

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


/-- A single-level ternary interpreter; each recursive call strictly reduces b. -/
def flatB (a b d : Nat) : Option HighLevelState :=
  if b=0 then some (.D a d)
  else if b%3=0 then flatB (a+1) (b/3-1) (d+2*b+3)
  else if b%3=1 then
    if a=0 then none else flatB (a-1) (b/3) (d+2*b+5)
  else if a=0 then flatB 0 (b/3) (d+2*b+3)
  else flatB (a-1) (b/3+1) (d+2*b+1)
termination_by b
decreasing_by
  all_goals
    have hdiv : b = 3*(b/3)+b%3 := by omega
    omega

/-- The one-level interpreter is exactly the original nested evaluator and
B-drain, for every natural triple, including successful results and failures. -/
theorem flatB_eq_drainB (b : Nat) : ∀ a d, flatB a b d = drainB a b d := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d
    rw [flatB]
    by_cases hz : b=0
    · simp [hz,drainB]
    · simp only [if_neg hz]
      let q := b/3
      have hdiv : b=3*q+b%3 := by dsimp [q]; omega
      by_cases h0 : b%3=0
      · simp only [if_pos h0]
        have hrep : b=3*q := by omega
        have hq : 0<q := by omega
        have hs : q-1<b := by omega
        have hh := ih (q-1) hs (a+1) (d+2*b+3)
        rw [hh]
        have hd : d+2*b+3=d+6*q+3 := by omega
        rw [hd]
        exact (hrep ▸ (drain_three a q d hq).symm)
      · simp only [if_neg h0]
        by_cases h1 : b%3=1
        · simp only [if_pos h1]
          have hrep : b=3*q+1 := by omega
          by_cases ha : a=0
          · simp only [if_pos ha]
            subst a
            simpa only [hrep] using (drain_three_one_zero q d).symm
          · simp only [if_neg ha]
            have hs : q<b := by omega
            have hh := ih q hs (a-1) (d+2*b+5)
            rw [hh]
            have hd : d+2*b+5=d+6*q+7 := by omega
            rw [hd]
            have hpos : 0<a := by omega
            exact (hrep ▸ (drain_three_one a q d hpos).symm)
        · simp only [if_neg h1]
          have hr : b%3=2 := by omega
          have hrep : b=3*q+2 := by omega
          by_cases ha : a=0
          · simp only [if_pos ha]
            subst a
            have hs : q<b := by omega
            have hh := ih q hs 0 (d+2*b+3)
            rw [hh]
            have hd : d+2*b+3=d+6*q+7 := by omega
            rw [hd]
            exact (hrep ▸ (drain_three_two_zero q d).symm)
          · simp only [if_neg ha]
            have hs : q+1<b := by omega
            have hh := ih (q+1) hs (a-1) (d+2*b+1)
            rw [hh]
            have hd : d+2*b+1=d+6*q+5 := by omega
            rw [hd]
            have hpos : 0<a := by omega
            exact (hrep ▸ (drain_three_two a q d hpos).symm)


/-- The binary code enumerates a complete family of bounded failures. -/
def lowerCode : Nat → Nat → Nat
  | 0, _ => 2
  | n+1, k => 3 * lowerCode n (k/2) - 1 + 2 * (k%2)

theorem lowerCode_bounds (n : Nat) :
    ∀ k, k < 2^n → 0 < lowerCode n k ∧ lowerCode n k < 3^(n+1) := by
  induction n with
  | zero =>
    intro k hk
    simp [lowerCode]
  | succ n ih =>
    intro k hk
    have htwo : 2^(n+1)=2*2^n := by rw [Nat.pow_succ]; omega
    have hthree : 3^(n+1+1)=3*3^(n+1) := by rw [Nat.pow_succ]; omega
    have hq : k/2<2^n := by omega
    have hmod : k%2<2 := Nat.mod_lt _ (by omega)
    obtain ⟨hl,hu⟩ := ih (k/2) hq
    simp only [lowerCode]
    omega

theorem bad_pow_false (n : Nat) : ¬bad (n+1) (3^(n+1)) := by
  have hp : 3^(n+1)=3*3^n := by rw [Nat.pow_succ]; omega
  have hm : 3^(n+1)%3=0 := by omega
  simp [bad,hm]

theorem bad_lowerCode (n : Nat) :
    ∀ k, k<2^n → bad (n+1) (lowerCode n k) := by
  induction n with
  | zero =>
    intro k hk
    have hkz : k=0 := by simpa using hk
    subst k
    simp [lowerCode,bad]
  | succ n ih =>
    intro k hk
    have hp2 : 2^(n+1)=2*2^n := by rw [Nat.pow_succ]; omega
    have hq : k/2 < 2^n := by omega
    have hr : k%2<2 := Nat.mod_lt _ (by omega)
    have hbad := ih (k/2) hq
    obtain ⟨hl,hu⟩ := lowerCode_bounds n (k/2) hq
    by_cases he : k%2=0
    · have hformula : lowerCode (n+1) k = 3*lowerCode n (k/2)-1 := by
        simp [lowerCode,he]
      rw [hformula]
      have hmod : (3*lowerCode n (k/2)-1)%3=2 := by omega
      have hdiv : (3*lowerCode n (k/2)-1)/3+1=lowerCode n (k/2) := by omega
      change _ ∨ ((3*lowerCode n (k/2)-1)%3=2 ∧
        bad (n+1) ((3*lowerCode n (k/2)-1)/3+1))
      exact Or.inr ⟨hmod, by simpa only [hdiv] using hbad⟩
    · have ho : k%2=1 := by omega
      have hformula : lowerCode (n+1) k = 3*lowerCode n (k/2)+1 := by
        simp [lowerCode,ho]
        omega
      rw [hformula]
      have hmod : (3*lowerCode n (k/2)+1)%3=1 := by omega
      have hdiv : (3*lowerCode n (k/2)+1)/3=lowerCode n (k/2) := by omega
      change ((3*lowerCode n (k/2)+1)%3=1 ∧
        bad (n+1) ((3*lowerCode n (k/2)+1)/3)) ∨ _
      exact Or.inl ⟨hmod, by simpa only [hdiv] using hbad⟩

/-- Every failure in the bounded interval has a binary code. -/
theorem lowerCode_of_bad (n : Nat) :
    ∀ b, b<3^(n+1) → bad (n+1) b →
      ∃ k, k<2^n ∧ lowerCode n k=b := by
  induction n with
  | zero =>
    intro b hb hbad
    have hb3 : b<3 := by simpa using hb
    change (b%3=1 ∧ b/3=1) ∨ (b%3=2 ∧ b/3+1=1) at hbad
    have hb2 : b=2 := by rcases hbad with ⟨hm,hd⟩ | ⟨hm,hd⟩ <;> omega
    exact ⟨0, by simp, by simpa [lowerCode] using hb2.symm⟩
  | succ n ih =>
    intro b hb hbad
    let q := b/3
    have hmod : b%3<3 := Nat.mod_lt _ (by omega)
    have hbdiv : b=3*q+b%3 := by dsimp [q]; omega
    have hpow : 3^(n+1+1)=3*3^(n+1) := by rw [Nat.pow_succ]; omega
    have hp2 : 2^(n+1)=2*2^n := by rw [Nat.pow_succ]; omega
    change (b%3=1 ∧ bad (n+1) (b/3)) ∨
      (b%3=2 ∧ bad (n+1) (b/3+1)) at hbad
    rcases hbad with ⟨hr,hh⟩ | ⟨hr,hh⟩
    · have hq : q<3^(n+1) := by dsimp [q]; omega
      obtain ⟨k,hk,he⟩ := ih q hq hh
      refine ⟨2*k+1, ?_, ?_⟩
      · omega
      · have hrem : (2*k+1)%2=1 := by omega
        have hdiv : (2*k+1)/2=k := by omega
        simp only [lowerCode,hrem,hdiv]
        have hx : 0<lowerCode n k := (lowerCode_bounds n k hk).1
        omega
    · have hqle : q+1≤3^(n+1) := by dsimp [q]; omega
      have hq : q+1<3^(n+1) := by
        by_cases hlt : q+1<3^(n+1)
        · exact hlt
        · have heq : q+1=3^(n+1) := by omega
          have hbadq : bad (n+1) (q+1) := by simpa [q] using hh
          exact False.elim ((by simpa only [heq] using hbadq : bad (n+1) (3^(n+1))) |> (bad_pow_false n))
      have hbadq : bad (n+1) (q+1) := by simpa [q] using hh
      obtain ⟨k,hk,he⟩ := ih (q+1) hq hbadq
      refine ⟨2*k, ?_, ?_⟩
      · omega
      · have hrem : (2*k)%2=0 := by omega
        have hdiv : (2*k)/2=k := by omega
        simp only [lowerCode,hrem,hdiv]
        have hx : 0<lowerCode n k := (lowerCode_bounds n k hk).1
        omega

theorem lowerCode_injective (n : Nat) :
    ∀ i j, i<2^n → j<2^n → lowerCode n i=lowerCode n j → i=j := by
  induction n with
  | zero =>
    intro i j hi hj he
    have hi0 : i=0 := by simpa using hi
    have hj0 : j=0 := by simpa using hj
    omega
  | succ n ih =>
    intro i j hi hj he
    have hp : 2^(n+1)=2*2^n := by rw [Nat.pow_succ]; omega
    have hir : i%2<2 := Nat.mod_lt _ (by omega)
    have hjr : j%2<2 := Nat.mod_lt _ (by omega)
    have hiq : i/2<2^n := by omega
    have hjq : j/2<2^n := by omega
    obtain ⟨hil,_⟩ := lowerCode_bounds n (i/2) hiq
    obtain ⟨hjl,_⟩ := lowerCode_bounds n (j/2) hjq
    have heq : 3*lowerCode n (i/2)-1+2*(i%2) =
        3*lowerCode n (j/2)-1+2*(j%2) := by simpa [lowerCode] using he
    have hrem : i%2=j%2 := by omega
    have hparent : lowerCode n (i/2) = lowerCode n (j/2) := by omega
    have hquot : i/2=j/2 := ih (i/2) (j/2) hiq hjq hparent
    omega

/-- Exact binary parametrization and unique code of every bounded failure:
the 2^n possible codes are in bijection with the failed b<3^(n+1). -/
theorem bounded_failure_binary_bijection (n b d : Nat) (hb : b<3^(n+1)) :
    drainB (n+1) b d = none ↔
      ∃ k : Nat, k<2^n ∧ lowerCode n k=b ∧
        (∀ k' : Nat, k'<2^n → lowerCode n k'=b → k'=k) := by
  have hbound : b≤3^(n+1) := by omega
  rw [drain_none_iff_bad (n+1) b d hbound]
  constructor
  · intro hbad
    obtain ⟨k,hk,he⟩ := lowerCode_of_bad n b hb hbad
    refine ⟨k,hk,he,?_⟩
    intro k' hk' he'
    exact lowerCode_injective n k' k hk' hk (he'.trans he.symm)
  · rintro ⟨k,hk,he,hunique⟩
    rw [←he]
    exact bad_lowerCode n k hk

#print axioms lowerCode_injective
#print axioms bounded_failure_binary_bijection
#print axioms lowerCode_of_bad
#print axioms bad_lowerCode


/-- The ternary-weighted sum of n binary digits. -/
def bitSum : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, k => k%2 + 3*bitSum n (k/2)

/-- Explicit closed form of every bounded failure code. -/
theorem lowerCode_closed (n : Nat) :
    ∀ k, k<2^n →
      2*lowerCode n k = 3^(n+1)+1+4*bitSum n k := by
  induction n with
  | zero =>
    intro k hk
    simp [lowerCode,bitSum]
  | succ n ih =>
    intro k hk
    have hp2 : 2^(n+1)=2*2^n := by rw [Nat.pow_succ]; omega
    have hq : k/2<2^n := by omega
    have hx : 0<lowerCode n (k/2) := (lowerCode_bounds n (k/2) hq).1
    have hi := ih (k/2) hq
    have hp3 : 3^(n+1+1)=3*3^(n+1) := by rw [Nat.pow_succ]; omega
    simp only [lowerCode,bitSum]
    omega

/-- A strictly stronger parity-respecting sharp safety threshold. -/
def shield : Nat → Nat
  | 0 => 4
  | a+1 => 3*shield a-1

theorem shield_ge_four (a : Nat) : 4 ≤ shield a := by
  induction a with
  | zero => simp [shield]
  | succ a ih =>
    simp only [shield]
    omega

theorem shield_mono_step (a : Nat) : shield a ≤ shield (a+1) := by
  have hl := shield_ge_four a
  simp only [shield]
  omega

theorem shield_parity (a : Nat) : shield a % 2 = a % 2 := by
  induction a with
  | zero => simp [shield]
  | succ a ih =>
    have hmin := shield_ge_four a
    have hrem : shield a%2<2 := Nat.mod_lt _ (by omega)
    have ha : a%2<2 := Nat.mod_lt _ (by omega)
    simp only [shield]
    omega

theorem shield_closed (a : Nat) : 2*shield a = 7*3^a+1 := by
  induction a with
  | zero => simp [shield]
  | succ a ih =>
    have hmin := shield_ge_four a
    have hp3 : 3^(a+1)=3*3^a := by rw [Nat.pow_succ]; omega
    simp only [shield]
    omega

/-- Exact all-input safety, without any restriction on the third counter. -/
theorem matching_parity_shield (b : Nat) :
    ∀ a d, b < shield a → b%2=a%2 →
      ∃ aa dd, drainB a b d = some (.D aa dd) := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d hbudget hparity
    by_cases hz : b=0
    · subst b
      exact ⟨a,d,by simp [drainB]⟩
    · let q := b/3
      have hrem : b%3<3 := Nat.mod_lt _ (by omega)
      have hdiv : b=3*q+b%3 := by dsimp [q]; omega
      by_cases h0 : b%3=0
      · have hrep : b=3*q := by omega
        have hq : 0<q := by omega
        have hsmall : q-1<b := by omega
        have hnew : q-1<shield (a+1) := by
          have hmono := shield_mono_step a
          omega
        have hpar : (q-1)%2=(a+1)%2 := by
          have hr : q%2<2 := Nat.mod_lt _ (by omega)
          have ha : a%2<2 := Nat.mod_lt _ (by omega)
          omega
        obtain ⟨aa,dd,hs⟩ := ih (q-1) hsmall (a+1) (d+6*q+3) hnew hpar
        refine ⟨aa,dd,?_⟩
        rw [hrep, drain_three a q d hq]
        exact hs
      · by_cases h1 : b%3=1
        · have hrep : b=3*q+1 := by omega
          cases a with
          | zero =>
            simp [shield] at hbudget
            omega
          | succ a =>
            have hsmall : q<b := by omega
            have hnew : q<shield a := by
              simp only [shield] at hbudget
              omega
            have hpar : q%2=a%2 := by
              have hr : q%2<2 := Nat.mod_lt _ (by omega)
              have ha : a%2<2 := Nat.mod_lt _ (by omega)
              omega
            obtain ⟨aa,dd,hs⟩ := ih q hsmall a (d+6*q+7) hnew hpar
            refine ⟨aa,dd,?_⟩
            rw [hrep, drain_three_one (a+1) q d (by omega)]
            exact hs
        · have h2 : b%3=2 := by omega
          have hrep : b=3*q+2 := by omega
          cases a with
          | zero =>
            have hsmall : q<b := by omega
            have hnew : q<shield 0 := by
              simp only [shield] at hbudget ⊢
              omega
            have hpar : q%2=0 := by
              have hr : q%2<2 := Nat.mod_lt _ (by omega)
              omega
            obtain ⟨aa,dd,hs⟩ := ih q hsmall 0 (d+6*q+7) hnew hpar
            refine ⟨aa,dd,?_⟩
            rw [hrep,drain_three_two_zero]
            exact hs
          | succ a =>
            have hsmall : q+1<b := by omega
            have hnew : q+1<shield a := by
              simp only [shield] at hbudget
              omega
            have hpar : (q+1)%2=a%2 := by
              have hr : q%2<2 := Nat.mod_lt _ (by omega)
              have ha : a%2<2 := Nat.mod_lt _ (by omega)
              omega
            obtain ⟨aa,dd,hs⟩ := ih (q+1) hsmall a (d+6*q+5) hnew hpar
            refine ⟨aa,dd,?_⟩
            rw [hrep,drain_three_two (a+1) q d (by omega)]
            exact hs

/-- Sharpness: at the threshold, despite matching parity, the drain fails. -/
theorem shield_first_failure (a : Nat) : ∀ d, drainB a (shield a) d=none := by
  induction a with
  | zero =>
    intro d
    have hs : shield 0 = 3*1+1 := by decide
    rw [hs]
    exact drain_three_one_zero 1 d
  | succ a ih =>
    intro d
    have hlarge := shield_ge_four a
    have heq : shield (a+1)=3*(shield a-1)+2 := by
      simp only [shield]
      omega
    rw [heq, drain_three_two (a+1) (shield a-1) d (by omega)]
    have ha : a+1-1=a := by omega
    have hb : shield a-1+1=shield a := by omega
    rw [ha,hb]
    exact ih (d+6*(shield a-1)+5)

#print axioms lowerCode_closed
#print axioms matching_parity_shield
#print axioms shield_first_failure
#print axioms shield_parity
#print axioms shield_closed


/-- The true #623 accelerated far-left odd branch gains a sharp parity shield.
This is universal over inputs; it does not establish blank-orbit reachability. -/
theorem highLevel_far_odd_shield (a d : Nat)
    (ha : a%2=0) (hd : d%2=1) (hleft : d+5≤a)
    (hbudget : d+3<shield (a-d-5)) :
    ∃ aa dd, highLevelNext (.D a d)=some (.D aa dd) := by
  have hz : a≠0 := by omega
  have hg : d%2=1 ∧ a≥d+5 := ⟨hd,hleft⟩
  have heven : (a-d-5)%2=0 := by omega
  have hblocks : (d+3)%2=0 := by omega
  obtain ⟨aa,dd,hr⟩ :=
    matching_parity_shield (d+3) (a-d-5) 5 hbudget (by omega)
  refine ⟨aa,dd,?_⟩
  simpa only [highLevelNext,if_neg hz,if_pos hg] using hr

/-- Complementary even-d far-left branch, again with a factor-seven wider
exponential guaranteed survival budget than the old ternary-ones prefix. -/
theorem highLevel_far_even_shield (a d : Nat)
    (ha : a%2=0) (hd : d%2=0) (hleft : d+3≤a)
    (hbudget : d+2<shield (a-d-2)) :
    ∃ aa dd, highLevelNext (.D a d)=some (.D aa dd) := by
  have hz : a≠0 := by omega
  have hnotodd : ¬(d%2=1 ∧ a≥d+5) := by omega
  have hg : d%2=0 ∧ a≥d+3 := ⟨hd,hleft⟩
  have heven : (a-d-2)%2=0 := by omega
  have hblocks : (d+2)%2=0 := by omega
  obtain ⟨aa,dd,hr⟩ :=
    matching_parity_shield (d+2) (a-d-2) 2 hbudget (by omega)
  refine ⟨aa,dd,?_⟩
  simpa only [highLevelNext,if_neg hz,if_neg hnotodd,if_pos hg] using hr

#print axioms highLevel_far_odd_shield
#print axioms highLevel_far_even_shield


/-- For every even n, the sharp odd-d boundary has an actual fatal
high-level transition, with even first counter as at the blank root. -/
theorem highLevel_far_odd_shield_sharp (n : Nat) (hne : n%2=0) :
    highLevelNext (.D (shield n+n+2) (shield n-3))=none := by
  let a := shield n+n+2
  let d := shield n-3
  have hs := shield_ge_four n
  have hsp : shield n%2=0 := by rw [shield_parity]; exact hne
  have hd : d%2=1 := by dsimp [d]; omega
  have hz : a≠0 := by dsimp [a]; omega
  have hbranch : d%2=1 ∧ a≥d+5 := by dsimp [a,d]; omega
  have heq1 : a-d-5=n := by dsimp [a,d]; omega
  have heq2 : d+3=shield n := by dsimp [d]; omega
  change highLevelNext (.D a d)=none
  have hnext : highLevelNext (.D a d)=drainB (a-d-5) (d+3) 5 := by
    simp only [highLevelNext,if_neg hz,if_pos hbranch]
  rw [hnext,heq1,heq2]
  exact shield_first_failure n 5

/-- Even-d fatal boundary, for every positive even n. -/
theorem highLevel_far_even_shield_sharp (n : Nat) (hne : n%2=0) (hn : 0<n) :
    highLevelNext (.D (shield n+n) (shield n-2))=none := by
  let a := shield n+n
  let d := shield n-2
  have hs := shield_ge_four n
  have hsp : shield n%2=0 := by rw [shield_parity]; exact hne
  have hd : d%2=0 := by dsimp [d]; omega
  have hz : a≠0 := by dsimp [a]; omega
  have hnotodd : ¬(d%2=1 ∧ a≥d+5) := by omega
  have hbranch : d%2=0 ∧ a≥d+3 := by dsimp [a,d]; omega
  have heq1 : a-d-2=n := by dsimp [a,d]; omega
  have heq2 : d+2=shield n := by dsimp [d]; omega
  change highLevelNext (.D a d)=none
  have hnext : highLevelNext (.D a d)=drainB (a-d-2) (d+2) 2 := by
    simp only [highLevelNext,if_neg hz,if_neg hnotodd,if_pos hbranch]
  rw [hnext,heq1,heq2]
  exact shield_first_failure n 2

#print axioms highLevel_far_odd_shield_sharp
#print axioms highLevel_far_even_shield_sharp


/-- Third original-machine safe sector: on the far right with odd d, the
entire B-drain has matching odd counter and block parity for even a. -/
theorem highLevel_right_odd_shield (a d : Nat)
    (ha : 0<a) (heven : a%2=0) (hd : d%2=1) (hright : a≤d)
    (hbudget : a-1 < shield (d+4-a)) :
    ∃ aa dd, highLevelNext (.D a d) = some (.D aa dd) := by
  have hz : a≠0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2≠1 := by omega
  have h4 : a≠d+2 := by omega
  have hfirst : (d+4-a)%2=1 := by omega
  have hblocks : (a-1)%2=1 := by omega
  obtain ⟨aa,dd,hs⟩ :=
    matching_parity_shield (a-1) (d+4-a) 3 hbudget (by omega)
  refine ⟨aa,dd,?_⟩
  simpa only [highLevelNext, if_neg hz, if_neg h1, if_neg h2,
    if_neg h3, if_neg h4, if_pos hd] using hs

/-- Sharp, root-parity-compatible fatal boundary for the right-odd sector.
It is a synthetic state, with no asserted blank-root reachability. -/
theorem highLevel_right_odd_shield_sharp (n : Nat)
    (hnodd : n%2=1) (hn : 5≤n) :
    highLevelNext (.D (shield n+1) (shield n+n-3))=none := by
  let a := shield n+1
  let d := shield n+n-3
  have hs := shield_ge_four n
  have hsp : shield n%2=1 := by rw [shield_parity]; exact hnodd
  have ha : 0<a := by dsimp [a]; omega
  have heven : a%2=0 := by dsimp [a]; omega
  have hd : d%2=1 := by dsimp [d]; omega
  have hright : a≤d := by dsimp [a,d]; omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2≠1 := by omega
  have h4 : a≠d+2 := by omega
  have hzero : a≠0 := by omega
  have hfirst : d+4-a=n := by dsimp [a,d]; omega
  have hblocks : a-1=shield n := by dsimp [a]; omega
  change highLevelNext (.D a d)=none
  have ht : highLevelNext (.D a d)=drainB (d+4-a) (a-1) 3 := by
    simp only [highLevelNext, if_neg hzero, if_neg h1, if_neg h2,
      if_neg h3, if_neg h4, if_pos hd]
  rw [ht,hfirst,hblocks]
  exact shield_first_failure n 3

#print axioms highLevel_right_odd_shield
#print axioms highLevel_right_odd_shield_sharp

#print axioms flatB_eq_drainB

#print axioms drain_three
#print axioms drain_three_one
#print axioms drain_three_one_zero
#print axioms drain_three_two_zero
#print axioms drain_three_two
#print axioms drain_none_iff_bad
end BB6.Agent49FlatDrainSource
