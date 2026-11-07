import Agent49DrainLinearLogSource

/-!
# Tight joint-mass bound for the authentic evaluator/drain recursion

The evaluator proof separates positive residual blocks from the zero-block
case. The drain induction then closes with the same ternary depth parameter.
All definitions are imported from the pinned Cryptids machine source through
Agent49DrainLinearLogSource.
-/

namespace BB6.Agent49JointMassSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49DrainLinearLogSource

/-- Positive residual blocks admit a depth split and a joint potential bound. -/
theorem evalA_joint_positive (n : Nat) :
    ∀ a k m aa bb dd,
      k < 3^n →
      evalA a k m = some (aa,bb,dd) →
      0 < bb →
      ∃ r s, r+s=n ∧ 0<r ∧ bb<3^s ∧ aa+dd+3*bb ≤ a+m+k+r := by
  induction n with
  | zero =>
      intro a k m aa bb dd hk he hbb
      have hk0 : k = 0 := by omega
      subst k
      cases a with
      | zero =>
          simp [evalA] at he
      | succ a =>
          simp [evalA] at he
          omega
  | succ n ih =>
      intro a k m aa bb dd hk he hbb
      have hq : k / 3 < 3^n := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).2
        simpa [Nat.pow_succ] using hk
      have hsplit : k = 3 * (k / 3) + k % 3 := by
        have := Nat.mod_add_div k 3
        omega
      by_cases h2 : k % 3 = 2
      · have he' : some (a+1,k/3,m) = some (aa,bb,dd) := by
          simpa [evalA, h2] using he
        injection he' with htuple
        rcases Prod.mk.inj htuple with ⟨hfirst,hrest⟩
        rcases Prod.mk.inj hrest with ⟨hsecond,hthird⟩
        subst aa bb dd
        refine ⟨1,n,by omega,by omega,hq,?_⟩
        omega
      · by_cases h0 : k % 3 = 0
        · by_cases ha : a = 0
          · simp [evalA, h2, h0, ha] at he
          · have he' : some (a-1,k/3,m+2) = some (aa,bb,dd) := by
              simpa [evalA, h2, h0, ha] using he
            injection he' with htuple
            rcases Prod.mk.inj htuple with ⟨hfirst,hrest⟩
            rcases Prod.mk.inj hrest with ⟨hsecond,hthird⟩
            subst aa bb dd
            refine ⟨1,n,by omega,by omega,hq,?_⟩
            omega
        · have h1 : k % 3 = 1 := by omega
          by_cases ha : a = 0
          · have he' : some (0,k/3,m) = some (aa,bb,dd) := by
              simpa [evalA, h2, h0, ha] using he
            injection he' with htuple
            rcases Prod.mk.inj htuple with ⟨hfirst,hrest⟩
            rcases Prod.mk.inj hrest with ⟨hsecond,hthird⟩
            subst aa bb dd
            refine ⟨1,n,by omega,by omega,hq,?_⟩
            omega
          · have he' : evalA (a-1) (k/3) (m+2*(k/3)+3) = some (aa,bb,dd) := by
              have he' := he
              rw [evalA] at he'
              simp only [if_neg h2, if_neg ha, if_neg h0] at he'
              exact he'
            obtain ⟨r,s,hrs,hrpos,hbb',hbound⟩ :=
              ih (a-1) (k/3) (m+2*(k/3)+3) aa bb dd hq he' hbb
            refine ⟨r+1,s,by omega,by omega,hbb',?_⟩
            omega

/-- Zero residual blocks have a separate sharp coarse bound. -/
theorem evalA_joint_zero (n : Nat) :
    ∀ a k m aa dd,
      k < 3^n →
      evalA a k m = some (aa,0,dd) →
      aa+dd ≤ a+m+k+n+1 := by
  induction n with
  | zero =>
      intro a k m aa dd hk he
      have hk0 : k = 0 := by omega
      subst k
      cases a with
      | zero =>
          simp [evalA] at he
      | succ a =>
          have he' : some (a,0,m+2) = some (aa,0,dd) := by
            simpa [evalA] using he
          have htuple := Option.some.inj he'
          rcases Prod.mk.inj htuple with ⟨haa,hrest⟩
          rcases Prod.mk.inj hrest with ⟨hbb,hdd⟩
          subst aa dd
          omega
  | succ n ih =>
      intro a k m aa dd hk he
      have hq : k / 3 < 3^n := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).2
        simpa [Nat.pow_succ] using hk
      have hsplit : k = 3 * (k / 3) + k % 3 := by
        have := Nat.mod_add_div k 3
        omega
      by_cases h2 : k % 3 = 2
      · have he' : some (a+1,k/3,m) = some (aa,0,dd) := by
          simpa [evalA, h2] using he
        have htuple := Option.some.inj he'
        rcases Prod.mk.inj htuple with ⟨haa,hrest⟩
        rcases Prod.mk.inj hrest with ⟨hq0,hdd⟩
        subst aa dd
        omega
      · by_cases h0 : k % 3 = 0
        · by_cases ha : a = 0
          · simp [evalA, h0, ha] at he
          · have he' : some (a-1,k/3,m+2) = some (aa,0,dd) := by
              simpa [evalA, h0, ha] using he
            have htuple := Option.some.inj he'
            rcases Prod.mk.inj htuple with ⟨haa,hrest⟩
            rcases Prod.mk.inj hrest with ⟨hq0,hdd⟩
            subst aa dd
            omega
        · have h1 : k % 3 = 1 := by omega
          by_cases ha : a = 0
          · have he' : some (0,k/3,m) = some (aa,0,dd) := by
              simpa [evalA, h2, h0, ha] using he
            have htuple := Option.some.inj he'
            rcases Prod.mk.inj htuple with ⟨haa,hrest⟩
            rcases Prod.mk.inj hrest with ⟨hq0,hdd⟩
            subst aa dd
            omega
          · have he' : evalA (a-1) (k/3) (m+2*(k/3)+3) = some (aa,0,dd) := by
              have he' := he
              rw [evalA] at he'
              simp only [if_neg h2, if_neg ha, if_neg h0] at he'
              exact he'
            have hbound := ih (a-1) (k/3) (m+2*(k/3)+3) aa dd hq he'
            omega

/-- A complete B-drain obeys the sharp joint-mass bound. -/
theorem drainB_joint_mass (n : Nat) :
    ∀ a b d aa dd,
      b < 3^n →
      drainB a b d = some (HighLevelState.D aa dd) →
      aa+dd ≤ a+d+3*b+3*n+1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro a b d aa dd hb hs
      by_cases hb0 : b = 0
      · have hs' : some (HighLevelState.D a d) = some (HighLevelState.D aa dd) := by
          simpa [drainB, hb0] using hs
        have htuple := Option.some.inj hs'
        rcases Prod.mk.inj htuple with ⟨haa,hdd⟩
        subst aa dd
        omega
      · have hbpos : 0 < b := by omega
        have hs' := hs
        rw [drainB] at hs'
        simp only [if_neg hb0] at hs'
        have hEval :
            ∃ p q r, evalA a (b-1) (d+2*b+3) = some (p,q,r) ∧
              q < b ∧ drainB p q r = some (HighLevelState.D aa dd) := by
          cases he : evalA a (b-1) (d+2*b+3) with
          | none =>
              simp [he] at hs'
          | some p =>
              rcases p with ⟨p,q,r⟩
              have hif :
                  (if q < b then drainB p q r else none)
                    = some (HighLevelState.D aa dd) := by
                simpa [he] using hs'
              have hq : q < b := by
                by_cases h : q < b
                · exact h
                · simp [h] at hif
              have hrec : drainB p q r = some (HighLevelState.D aa dd) := by
                simpa [hq] using hif
              exact ⟨p,q,r,by simpa using he,hq,hrec⟩
        rcases hEval with ⟨p,q,r,he,hq,hrec⟩
        have hk : b-1 < 3^n := by omega
        by_cases hq0 : q = 0
        · have hn : 0 < n := by
            by_cases hn0 : n = 0
            · subst n
              simp at hb
              omega
            · omega
          have he0 : evalA a (b-1) (d+2*b+3) = some (p,0,r) := by
            simpa [hq0] using he
          have hzero := evalA_joint_zero n a (b-1) (d+2*b+3) p r hk he0
          have hrec' : some (HighLevelState.D p r) = some (HighLevelState.D aa dd) := by
            simpa [drainB, hq0] using hrec
          have htuple := Option.some.inj hrec'
          injection htuple with haa hdd
          subst aa dd
          omega
        · have hqpos : 0 < q := by omega
          obtain ⟨u,v,huv,hu,hv,hbound⟩ :=
            evalA_joint_positive n a (b-1) (d+2*b+3) p q r hk he hqpos
          have hvlt : v < n := by omega
          have hrecBound := ih v hvlt p q r aa dd hv hrec
          calc
            aa+dd ≤ p+r+3*q+3*v+1 := hrecBound
            _ ≤ a+d+3*b+3*n+1 := by omega


/-- The sharp-block family lies below the next ternary power. -/
theorem sharpBlock_lt_pow (n : Nat) : sharpBlock n < 3^(n+1) := by
  induction n with
  | zero =>
      simp [sharpBlock]
  | succ n ih =>
      have hle : 3*(sharpBlock n + 1) ≤ 3*3^(n+1) :=
        Nat.mul_le_mul_left 3 (Nat.succ_le_of_lt ih)
      have hbound : 3*sharpBlock n + 1 < 3*3^(n+1) := by omega
      simpa [sharpBlock, Nat.pow_succ, Nat.mul_comm] using hbound

/-- The joint-mass upper bound is attained by the existing sharp-block family. -/
theorem drainB_joint_mass_sharp (n d : Nat) :
    sharpBlock n < 3^(n+1) ∧
    ∃ dd, drainB (n+2) (sharpBlock n) d = some (HighLevelState.D 0 dd) ∧
      dd = (n+2)+d+3*sharpBlock n+3*(n+1)+1 := by
  constructor
  · exact sharpBlock_lt_pow n
  · refine ⟨d+3*sharpBlock n+4*(n+1)+2, drainB_sharp_witness n d, ?_⟩
    omega

#print axioms evalA_joint_positive
#print axioms evalA_joint_zero
#print axioms drainB_joint_mass
#print axioms sharpBlock_lt_pow
#print axioms drainB_joint_mass_sharp

end BB6.Agent49JointMassSource
