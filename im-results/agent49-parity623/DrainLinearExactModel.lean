import Std

/-!
Standalone verification harness for Agent 49's #623 drain bounds.

The definitions of evalA and drainB below are copied exactly from the
upstream machine file
google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b,
BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean.

This file compiles with Lean 4.36.0-rc2 and imports only Std. The two
one-step terminal power-gap inequalities are supplied as hypotheses in the
terminal arithmetic lemmas; the source-shaped module
DrainLinearTerminalSource.lean instantiates them with the pinned
next_none_requires_pow_gap theorem. This harness is not a substitute for
the repository's full source-import CI check.
-/

inductive HighLevelState where
  | D (a d : Nat)
  deriving Repr, DecidableEq

def evalA (a k m : Nat) : Option (Nat × Nat × Nat) :=
  if k % 3 = 2 then some (a + 1, k / 3, m)
  else if a = 0 then
    if k % 3 = 0 then none else some (0, k / 3, m)
  else if k % 3 = 0 then some (a - 1, k / 3, m + 2)
  else evalA (a - 1) (k / 3) (m + 2 * (k / 3) + 3)
termination_by a
decreasing_by omega

def drainB (a b d : Nat) : Option HighLevelState :=
  if b = 0 then some (.D a d)
  else
    (evalA a (b - 1) (d + 2 * b + 3)).bind fun p =>
      if p.2.1 < b then drainB p.1 p.2.1 p.2.2 else none
termination_by b
decreasing_by omega

theorem evalA_upper_log (n : Nat) :
    ∀ a k m aa bb dd : Nat, k < 3^n →
    evalA a k m = some (aa,bb,dd) → dd+3*bb ≤ m+k+2*(n+1) := by
  induction n with
  | zero =>
    intro a k m aa bb dd hk hs
    have hk0 : k=0 := by simpa using hk
    subst k
    rw [evalA] at hs
    by_cases ha : a=0
    · simp [ha] at hs
    · simp [ha] at hs
      cases hs
      omega
  | succ n ih =>
    intro a k m aa bb dd hk hs
    rw [evalA] at hs
    by_cases h2 : k%3=2
    · simp [h2] at hs
      cases hs
      omega
    · by_cases ha : a=0
      · by_cases h0 : k%3=0
        · simp [h2,ha,h0] at hs
        · simp [h2,ha,h0] at hs
          cases hs
          omega
      · by_cases h0 : k%3=0
        · simp [h2,ha,h0] at hs
          cases hs
          omega
        · simp [h2,ha,h0] at hs
          have hpow : 3^(n+1)=3*3^n := by rw [Nat.pow_succ]; omega
          have hq : k/3<3^n := by omega
          have hr := ih (a-1) (k/3) (m+2*(k/3)+3) aa bb dd hq hs
          omega

theorem evalA_first_lower_log (n : Nat) :
    ∀ a k m aa bb dd : Nat,
      k < 3^n →
      evalA a k m = some (aa,bb,dd) →
      aa+n+1≥a := by
  induction n with
  | zero =>
      intro a k m aa bb dd hk hs
      have hk0 : k=0 := by simpa using hk
      subst k
      rw [evalA] at hs
      by_cases ha : a=0
      · simp [ha] at hs
      · simp [ha] at hs
        cases hs
        omega
  | succ n ih =>
      intro a k m aa bb dd hk hs
      rw [evalA] at hs
      by_cases h2 : k%3=2
      · simp [h2] at hs
        cases hs
        omega
      · by_cases ha : a=0
        · by_cases h0 : k%3=0
          · simp [h2,ha,h0] at hs
          · simp [h2,ha,h0] at hs
            cases hs
            omega
        · by_cases h0 : k%3=0
          · simp [h2,ha,h0] at hs
            cases hs
            omega
          · simp [h2,ha,h0] at hs
            have hpow : 3^(n+1)=3*3^n := by rw [Nat.pow_succ]; omega
            have hq : k/3<3^n := by omega
            have hr := ih (a-1) (k/3) (m+2*(k/3)+3) aa bb dd hq hs
            omega

theorem evalA_positive_depth (n : Nat) :
    ∀ a k m aa bb dd : Nat,
      k < 3^n → 0 < bb →
      evalA a k m = some (aa,bb,dd) →
      ∃ r s : Nat,
        r+s=n ∧ 0<r ∧ bb<3^s ∧ aa+r≥a ∧ dd+3*bb≤m+k+2*r := by
  induction n with
  | zero =>
      intro a k m aa bb dd hk hbb hs
      have hk0 : k=0 := by simpa using hk
      subst k
      rw [evalA] at hs
      by_cases ha : a=0
      · simp [ha] at hs
      · simp [ha] at hs
        cases hs
        omega
  | succ n ih =>
      intro a k m aa bb dd hk hbb hs
      rw [evalA] at hs
      by_cases h2 : k%3=2
      · simp [h2] at hs
        rcases hs with ⟨rfl, rfl, rfl⟩
        have hpow : 3^(n+1)=3*3^n := by rw [Nat.pow_succ]; omega
        have hq : k/3<3^n := by omega
        refine ⟨1,n,by omega,by omega,hq,by omega,by omega⟩
      · by_cases ha : a=0
        · by_cases h0 : k%3=0
          · simp [h2,ha,h0] at hs
          · simp [h2,ha,h0] at hs
            rcases hs with ⟨rfl, rfl, rfl⟩
            have hpow : 3^(n+1)=3*3^n := by rw [Nat.pow_succ]; omega
            have hq : k/3<3^n := by omega
            refine ⟨1,n,by omega,by omega,hq,by omega,by omega⟩
        · by_cases h0 : k%3=0
          · simp [h2,ha,h0] at hs
            rcases hs with ⟨rfl, rfl, rfl⟩
            have hpow : 3^(n+1)=3*3^n := by rw [Nat.pow_succ]; omega
            have hq : k/3<3^n := by omega
            refine ⟨1,n,by omega,by omega,hq,by omega,by omega⟩
          · simp [h2,ha,h0] at hs
            have hpow : 3^(n+1)=3*3^n := by rw [Nat.pow_succ]; omega
            have hq : k/3<3^n := by omega
            have hr := ih (a-1) (k/3) (m+2*(k/3)+3)
              aa bb dd hq hbb hs
            rcases hr with ⟨r,s,hrs,hrpos,hbs,hfirst,hpot⟩
            refine ⟨r+1,s,by omega,by omega,hbs,by omega,?_⟩
            omega

theorem drainB_upper_linear_log (n : Nat) :
    ∀ a b d aa dd : Nat, b<3^n →
      drainB a b d = some (.D aa dd) →
      dd ≤ d+3*b+4*n+2 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro a b d aa dd hb hs
      by_cases hb0 : b=0
      · subst b
        simp [drainB] at hs
        cases hs
        omega
      · have hn : 0<n := by
          cases n with
          | zero =>
              simp at hb
              omega
          | succ n => omega
        rw [drainB] at hs
        simp only [if_neg hb0] at hs
        cases hev : evalA a (b-1) (d+2*b+3) with
        | none => simp [hev] at hs
        | some p =>
            rcases p with ⟨a1,b1,d1⟩
            simp only [hev,Option.bind_some] at hs
            by_cases hlt : b1<b
            · simp only [if_pos hlt] at hs
              by_cases hb1 : b1=0
              · subst b1
                simp [drainB] at hs
                cases hs
                have hlog := evalA_upper_log n a (b-1) (d+2*b+3)
                  a1 0 d1 (by omega) hev
                omega
              · have hdepth := evalA_positive_depth n a (b-1)
                  (d+2*b+3) a1 b1 d1 (by omega) (by omega) hev
                rcases hdepth with ⟨r,s,hrs,hrpos,hbs,hfirst,hpot⟩
                have hsn : s<n := by omega
                have hrec := ih s hsn a1 b1 d1 aa dd hbs hs
                omega
            · simp [hlt] at hs

theorem drainB_first_lower_log (n : Nat) :
    ∀ a b d aa dd : Nat, b<3^n →
      drainB a b d = some (.D aa dd) →
      aa+n+1≥a := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro a b d aa dd hb hs
      by_cases hb0 : b=0
      · subst b
        simp [drainB] at hs
        cases hs
        omega
      · rw [drainB] at hs
        simp only [if_neg hb0] at hs
        cases hev : evalA a (b-1) (d+2*b+3) with
        | none => simp [hev] at hs
        | some p =>
            rcases p with ⟨a1,b1,d1⟩
            simp only [hev,Option.bind_some] at hs
            by_cases hlt : b1<b
            · simp only [if_pos hlt] at hs
              by_cases hb1 : b1=0
              · subst b1
                simp [drainB] at hs
                cases hs
                have hfirst := evalA_first_lower_log n a (b-1)
                  (d+2*b+3) a1 0 d1 (by omega) hev
                omega
              · have hdepth := evalA_positive_depth n a (b-1)
                  (d+2*b+3) a1 b1 d1 (by omega) (by omega) hev
                rcases hdepth with ⟨r,s,hrs,hrpos,hbs,hfirst,hpot⟩
                have hsn : s<n := by omega
                have hrec := ih s hsn a1 b1 d1 aa dd hbs hs
                omega
            · simp [hlt] at hs


theorem terminal_interval_arithmetic (a b d n aa dd : Nat)
    (hs : drainB a b d = some (.D aa dd))
    (hb : b<3^n)
    (hfirstUpper : aa≤a+n)
    (hthirdLower : d+3*b≤dd)
    (hgate1 : 3^(dd-aa-5) ≤ 2*(aa+dd)+5)
    (hgate2 : 3^(aa-dd-5) ≤ 2*(aa+dd)+5) :
    3^((d+3*b)-(a+n)-5) ≤ 2*(a+d+3*b+5*n+2)+5 ∧
    3^(a-d-3*b-5*n-8) ≤ 2*(a+d+3*b+5*n+2)+5 := by
  have hl := drainB_first_lower_log n a b d aa dd hb hs
  have hu := drainB_upper_linear_log n a b d aa dd hb hs
  have hm : aa+dd ≤ a+d+3*b+5*n+2 := by omega
  constructor
  · have hr : (d+3*b)-(a+n)-5 ≤ dd-aa-5 := by omega
    have hp := Nat.pow_le_pow_right (by omega : 0<3) hr
    omega
  · have hr : (a-d-3*b-5*n-8) ≤ aa-dd-5 := by omega
    have hp := Nat.pow_le_pow_right (by omega : 0<3) hr
    omega

#print axioms evalA_first_lower_log
#print axioms evalA_positive_depth
#print axioms drainB_upper_linear_log
#print axioms drainB_first_lower_log
#print axioms terminal_interval_arithmetic


def sharpBlock : Nat → Nat
  | 0 => 2
  | n+1 => 3*sharpBlock n + 1

theorem drainB_sharp_witness (n d : Nat) :
    drainB (n+2) (sharpBlock n) d =
      some (.D 0 (d+3*sharpBlock n+4*(n+1)+2)) := by
  induction n generalizing d with
  | zero =>
      change drainB 2 2 d = some (.D 0 (d+12))
      have hEval : evalA 2 1 (d+7) = some (0,0,d+12) := by
        simp [evalA]
      rw [drainB.eq_1]
      rw [if_neg (by decide : 2 ≠ 0)]
      rw [hEval]
      simp only [Option.bind_some, if_pos (by decide : 0 < 2)]
      simp [drainB]
  | succ n ih =>
      have hlt : sharpBlock n < 3*sharpBlock n+1 := by omega
      have hEval :
          evalA (n+3) ((3*sharpBlock n+1)-1)
            (d+2*(3*sharpBlock n+1)+3) =
              some (n+2, sharpBlock n, d+2*(3*sharpBlock n+1)+5) := by
        simp [evalA]
      change drainB (n+3) (3*sharpBlock n+1) d =
        some (.D 0 (d+3*sharpBlock (n+1)+4*((n+1)+1)+2))
      rw [drainB.eq_1]
      rw [if_neg (by omega : 3*sharpBlock n+1 ≠ 0)]
      rw [hEval]
      simp only [Option.bind_some, if_pos hlt]
      calc
        drainB (n+2) (sharpBlock n) (d+2*(3*sharpBlock n+1)+5) =
            some (.D 0 ((d+2*(3*sharpBlock n+1)+5)+3*sharpBlock n+4*(n+1)+2)) :=
          ih (d+2*(3*sharpBlock n+1)+5)
        _ = some (.D 0 (d+3*sharpBlock (n+1)+4*((n+1)+1)+2)) := by
          simp [sharpBlock]
          omega

#print axioms drainB_sharp_witness


theorem evalA_first_upper_one (a : Nat) :
    ∀ k m aa bb dd : Nat,
      evalA a k m = some (aa,bb,dd) → aa≤a+1 := by
  induction a with
  | zero =>
      intro k m aa bb dd hs
      rw [evalA] at hs
      by_cases h2 : k%3=2
      · simp [h2] at hs
        rcases hs with ⟨rfl,rfl,rfl⟩
        omega
      · by_cases h0 : k%3=0
        · simp [h2,h0] at hs
        · simp [h2,h0] at hs
          rcases hs with ⟨rfl,rfl,rfl⟩
          omega
  | succ a ih =>
      intro k m aa bb dd hs
      rw [evalA] at hs
      by_cases h2 : k%3=2
      · simp [h2] at hs
        rcases hs with ⟨rfl,rfl,rfl⟩
        omega
      · by_cases h0 : k%3=0
        · simp [h2,h0] at hs
          rcases hs with ⟨rfl,rfl,rfl⟩
          omega
        · simp [h2,h0] at hs
          have hr := ih (k/3) (m+2*(k/3)+3) aa bb dd hs
          omega

theorem evalA_third_lower (a : Nat) :
    ∀ k m aa bb dd : Nat,
      evalA a k m = some (aa,bb,dd) → m+k≤dd+3*bb+2 := by
  induction a with
  | zero =>
      intro k m aa bb dd hs
      rw [evalA] at hs
      by_cases h2 : k%3=2
      · simp [h2] at hs
        rcases hs with ⟨rfl,rfl,rfl⟩
        omega
      · by_cases h0 : k%3=0
        · simp [h2,h0] at hs
        · simp [h2,h0] at hs
          rcases hs with ⟨rfl,rfl,rfl⟩
          omega
  | succ a ih =>
      intro k m aa bb dd hs
      rw [evalA] at hs
      by_cases h2 : k%3=2
      · simp [h2] at hs
        rcases hs with ⟨rfl,rfl,rfl⟩
        omega
      · by_cases h0 : k%3=0
        · simp [h2,h0] at hs
          rcases hs with ⟨rfl,rfl,rfl⟩
          omega
        · simp [h2,h0] at hs
          have hr := ih (k/3) (m+2*(k/3)+3) aa bb dd hs
          omega


theorem terminal_balance_nat (a b d n K aa dd : Nat)
    (hs : drainB a b d = some (.D aa dd))
    (hb : b<3^n)
    (hfirstUpper : aa≤a+n)
    (hthirdLower : d+3*b≤dd)
    (hgate1 : 3^(dd-aa-5) ≤ 2*(aa+dd)+5)
    (hgate2 : 3^(aa-dd-5) ≤ 2*(aa+dd)+5)
    (hK : 2*(a+d+3*b+5*n+2)+5 < 3^K) :
    d+3*b ≤ a+n+K+4 ∧ a ≤ d+3*b+5*n+K+7 := by
  have hi := terminal_interval_arithmetic a b d n aa dd hs hb
    hfirstUpper hthirdLower hgate1 hgate2
  constructor
  · by_cases h : d+3*b ≤ a+n+K+4
    · exact h
    · have hexp : K ≤ (d+3*b)-(a+n)-5 := by omega
      have hp := Nat.pow_le_pow_right (by omega : 0<3) hexp
      omega
  · by_cases h : a ≤ d+3*b+5*n+K+7
    · exact h
    · have hexp : K ≤ a-d-3*b-5*n-8 := by omega
      have hp := Nat.pow_le_pow_right (by omega : 0<3) hexp
      omega


theorem evenRight_terminal_balance_local
    (a d n0 n K x b y aa dd : Nat)
    (hRight : a≤d)
    (ha : a<3^n0)
    (hbpos : 0<b)
    (hEval : evalA (d+1-a) a (2*a+5) = some (x,b,y))
    (hDrain : drainB x b y = some (.D aa dd))
    (hb : b<3^n)
    (hfirstDrain : aa≤x+n)
    (hthirdDrain : y+3*b≤dd)
    (hgate1 : 3^(dd-aa-5) ≤ 2*(aa+dd)+5)
    (hgate2 : 3^(aa-dd-5) ≤ 2*(aa+dd)+5)
    (hK : 2*(x+y+3*b+5*n+2)+5 < 3^K) :
    4*a≤d+n+K+3 ∧ d≤4*a+5*n+K+11+3*n0 := by
  obtain ⟨r,s,hrs,hrpos,hbs,hfirst,hpot⟩ :=
    evalA_positive_depth n0 (d+1-a) a (2*a+5) x b y ha hbpos hEval
  have hfirstUpper := evalA_first_upper_one (d+1-a) a (2*a+5) x b y hEval
  have hthirdLower := evalA_third_lower (d+1-a) a (2*a+5) x b y hEval
  have hbal := terminal_balance_nat x b y n K aa dd hDrain hb
    hfirstDrain hthirdDrain hgate1 hgate2 hK
  omega


theorem oddLeft_ray_local (d t n K : Nat)
    (hbal : 5+3*(d+3) ≤ (d+t+4)+n+K+4 ∧
      d+t+4 ≤ 5+3*(d+3)+5*n+K+7) :
    2*d+6≤t+n+K ∧ t≤2*d+5*n+K+17 := by
  omega

theorem evenLeft_ray_local (d t n K : Nat)
    (hbal : 2+3*(d+2) ≤ (d+t+3)+n+K+4 ∧
      d+t+3 ≤ 2+3*(d+2)+5*n+K+7) :
    2*d+1≤t+n+K ∧ t≤2*d+5*n+K+12 := by
  omega

theorem oddRight_ray_local (a t n K : Nat)
    (ha : 1≤a)
    (hbal : 3+3*(a-1) ≤ (a+2*t+5)+n+K+4 ∧
      a+2*t+5 ≤ 3+3*(a-1)+5*n+K+7) :
    2*a≤2*t+n+K+9 ∧ 2*t≤2*a+5*n+K+2 := by
  omega


theorem terminal_gap_bound_local (x y K M : Nat)
    (hEven : x%2=0)
    (hgate1 : 3^(y-x-5) ≤ 2*(x+y)+5)
    (hgate2 : 3^(x-y-5) ≤ 2*(x+y)+5)
    (hmass : x+y≤M)
    (hK : 2*M+5<3^K) :
    x≤y+K+4 ∧ y≤x+K+4 := by
  constructor
  · by_cases h : x≤y+K+4
    · exact h
    · have hexp : K≤x-y-5 := by omega
      have hp := Nat.pow_le_pow_right (by omega : 0<3) hexp
      omega
  · by_cases h : y≤x+K+4
    · exact h
    · have hexp : K≤y-x-5 := by omega
      have hp := Nat.pow_le_pow_right (by omega : 0<3) hexp
      omega

theorem evenRight_zero_block_terminal_local
    (a d n0 K x y : Nat)
    (hRight : a≤d)
    (ha : a<3^n0)
    (hEval : evalA (d+1-a) a (2*a+5) = some (x,0,y))
    (hEven : x%2=0)
    (hgate1 : 3^(y-x-5) ≤ 2*(x+y)+5)
    (hgate2 : 3^(x-y-5) ≤ 2*(x+y)+5)
    (hK : 2*(d+2*a+9+2*n0)+5 < 3^K) :
    4*a≤d+K+3 ∧ d≤4*a+K+11+3*n0 := by
  have hfirstUpper := evalA_first_upper_one (d+1-a) a (2*a+5) x 0 y hEval
  have hfirstLower := evalA_first_lower_log n0 (d+1-a) a (2*a+5)
    x 0 y ha hEval
  have hthirdLower := evalA_third_lower (d+1-a) a (2*a+5) x 0 y hEval
  have hthirdUpper := evalA_upper_log n0 (d+1-a) a (2*a+5)
    x 0 y ha hEval
  have hmass : x+y≤d+2*a+9+2*n0 := by omega
  have hgap := terminal_gap_bound_local x y K (d+2*a+9+2*n0)
    hEven hgate1 hgate2 hmass hK
  omega
