import Agent49CanonicalRayCocycleSource
import Agent22ExactDrainCocycleSource
import Agent22GapScaleExactArithmetic

/-!
# Exact quadratic Lyapunov gain on the four canonical #623 rays

The source-weighted drain identity counts outer drain iterations.  A second
bound, proved simultaneously with that identity, says the final first
counter is at most the initial first counter plus that iteration count.
Together they force a positive cone for the exact canonical gap corrections.
The common quadratic form then increases on every successful canonical-ray
transition, without assuming that the output remains on the same side of
the diagonal or that the leading projective branch is selected.
-/

namespace BB6.Agent49GapScaleResidualSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49CanonicalRayCocycleSource
open BB6.Agent22ExactDrainCocycleSource
open BB6.Agent22GapScaleExactArithmetic

/-- One evaluator call raises its first counter by at most one. -/
theorem evalA_first_upper_one (a : Nat) :
    ∀ k m aa bb dd : Nat,
      evalA a k m = some (aa,bb,dd) → aa ≤ a+1 := by
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

/-- The exact weighted drain iteration count also bounds first-counter gain:
each outer call can increase the first counter by at most one. -/
theorem drainB_first_le_iter (b : Nat) :
    ∀ a d aa dd : Nat,
      b ≤ ternaryOnes a →
      drainB a b d = some (.D aa dd) →
      ∃ r : Nat,
        aa ≤ a+r ∧ 2*aa+dd = 2*a+d+3*b+2*r := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
      intro a d aa dd hbudget hs
      rw [drainB] at hs
      by_cases hb : b=0
      · simp [hb] at hs
        cases hs
        exact ⟨0,by omega,by omega⟩
      · have hstrict : b-1 < ternaryOnes a := by omega
        simp only [if_neg hb] at hs
        cases he : evalA a (b-1) (d+2*b+3) with
        | none =>
            simp [he] at hs
        | some p =>
            rcases p with ⟨a1,b1,d1⟩
            simp only [he,Option.bind_some] at hs
            by_cases hlt : b1 < b
            · simp only [if_pos hlt] at hs
              have hbudget1 : b1 ≤ ternaryOnes a1 := by
                obtain ⟨a2,b2,d2,he2,hb2⟩ :=
                  evalA_ones_budget a (b-1) (d+2*b+3) hstrict
                rw [he] at he2
                cases he2
                exact hb2
              obtain ⟨r,hfirst,hpot⟩ :=
                ih b1 hlt a1 d1 aa dd hbudget1 hs
              have hfirstEval :=
                evalA_first_upper_one a (b-1) (d+2*b+3) a1 b1 d1 he
              have hpotEval :=
                evalA_weighted_exact a (b-1) (d+2*b+3)
                  a1 b1 d1 hstrict he
              refine ⟨r+1,?_,?_⟩
              · omega
              · omega
            · simp [hlt] at hs

def beta (B c v : Nat) : Int := (B : Int) - (c : Int) - (v : Int)
def delta (E m : Nat) : Int := (E : Int) - 3*(m : Int)

/-- Left-odd canonical base correction cone. -/
theorem left_odd_residual_bounds (k d B E : Nat)
    (hbudget : d+3 ≤ ternaryOnes k)
    (hbase : drainB k (d+3) 5 = some (.D B E)) :
    (4 : Int) ≤ 2*beta B 5 k + delta E d ∧
    (9 : Int) ≤ beta B 5 k + delta E d ∧
    (23 : Int) ≤ beta B 5 k + 2*delta E d := by
  obtain ⟨r,hfirst,hpot⟩ := drainB_first_le_iter (d+3) k 5 B E hbudget hbase
  have hpotI : 2*(B : Int)+(E : Int) =
      2*(k : Int)+5+3*((d : Int)+3)+2*(r : Int) := by
    exact_mod_cast hpot
  have hfirstI : (B : Int) ≤ (k : Int)+(r : Int) := by
    exact_mod_cast hfirst
  simp [beta,delta]
  constructor
  · omega
  constructor
  · omega
  · omega

/-- Left-even canonical base correction cone. -/
theorem left_even_residual_bounds (k d B E : Nat)
    (hbudget : d+2 ≤ ternaryOnes k)
    (hbase : drainB k (d+2) 2 = some (.D B E)) :
    (4 : Int) ≤ 2*beta B 2 k + delta E d ∧
    (6 : Int) ≤ beta B 2 k + delta E d ∧
    (14 : Int) ≤ beta B 2 k + 2*delta E d := by
  obtain ⟨r,hfirst,hpot⟩ := drainB_first_le_iter (d+2) k 2 B E hbudget hbase
  have hpotI : 2*(B : Int)+(E : Int) =
      2*(k : Int)+2+3*((d : Int)+2)+2*(r : Int) := by
    exact_mod_cast hpot
  have hfirstI : (B : Int) ≤ (k : Int)+(r : Int) := by
    exact_mod_cast hfirst
  simp [beta,delta]
  constructor
  · omega
  constructor
  · omega
  · omega

/-- Right-odd canonical base correction cone. -/
theorem right_odd_residual_bounds (k a B E : Nat)
    (hbudget : a-1 ≤ ternaryOnes (2*k+5))
    (hbase : drainB (2*k+5) (a-1) 3 = some (.D B E)) :
    (8 : Int) ≤ 2*beta B 1 (2*k) + delta E a ∧
    (4 : Int) ≤ beta B 1 (2*k) + delta E a ∧
    (4 : Int) ≤ beta B 1 (2*k) + 2*delta E a := by
  obtain ⟨r,hfirst,hpot⟩ :=
    drainB_first_le_iter (a-1) (2*k+5) 3 B E hbudget hbase
  have hpotI : 2*(B : Int)+(E : Int) =
      2*((2*k+5 : Nat) : Int)+3+3*((a-1 : Nat) : Int)+2*(r : Int) := by
    exact_mod_cast hpot
  have hfirstI : (B : Int) ≤ (2*k+5 : Int)+(r : Int) := by
    exact_mod_cast hfirst
  have ha : 1 ≤ a := by
    by_contra h
    have : a=0 := by omega
    subst a
    simp at hbudget
  simp [beta,delta]
  constructor
  · omega
  constructor
  · omega
  · omega

/-- Right-even canonical base correction cone, including the initial evalA. -/
theorem right_even_residual_bounds (k a a1 b1 d1 B E : Nat)
    (hbudget : a < ternaryOnes (2*k+3))
    (heval : evalA (2*k+3) a (2*a+5) = some (a1,b1,d1))
    (hbase : drainB a1 b1 d1 = some (.D B E)) :
    (7 : Int) ≤ 2*beta B 2 (2*k) + delta E a ∧
    (5 : Int) ≤ beta B 2 (2*k) + delta E a ∧
    (8 : Int) ≤ beta B 2 (2*k) + 2*delta E a := by
  have hbudget1 : b1 ≤ ternaryOnes a1 := by
    obtain ⟨a2,b2,d2,he,hb⟩ :=
      evalA_ones_budget (2*k+3) a (2*a+5) hbudget
    rw [heval] at he
    cases he
    exact hb
  obtain ⟨r,hfirst,hpot⟩ :=
    drainB_first_le_iter b1 a1 d1 B E hbudget1 hbase
  have hfirstEval : a1 ≤ 2*k+4 :=
    evalA_first_upper_one (2*k+3) a (2*a+5) a1 b1 d1 heval
  have hpotEval :=
    evalA_weighted_exact (2*k+3) a (2*a+5) a1 b1 d1 hbudget heval
  have hpotI : 2*(B : Int)+(E : Int) =
      2*((2*k+3 : Nat) : Int)+3*(a : Int)+(2*a+5 : Int)+2*(r : Int) := by
    exact_mod_cast (by omega : 2*B+E =
      2*(2*k+3)+3*a+(2*a+5)+2*r)
  have hfirstI : (B : Int) ≤ (2*k+4 : Int)+(r : Int) := by
    exact_mod_cast (by omega : B ≤ 2*k+4+r)
  simp [beta,delta]
  constructor
  · omega
  constructor
  · omega
  · omega

/-- The common positive-definite quadratic form. -/
def quadraticGap (g m : Int) : Int := g^2+9*g*m+21*m^2

theorem quadraticGap_nonneg (g m : Int) : 0 ≤ quadraticGap g m := by
  have h1 : 0 ≤ (2*g+9*m)^2 := sq_nonneg (2*g+9*m)
  have h2 : 0 ≤ m^2 := sq_nonneg m
  unfold quadraticGap
  nlinarith

theorem quadraticGap_left_expansion (g m eg em : Int) :
    quadraticGap (g-9*m+eg) (3*m+em) =
      quadraticGap g m + 6*m^2 + quadraticGap eg em +
        g*(2*eg+9*em) + 9*m*(eg+5*em) := by
  unfold quadraticGap
  ring

theorem quadraticGap_right_expansion (g m eg em : Int) :
    quadraticGap (-4*g-9*m+eg) (3*m+g+em) =
      quadraticGap g m + 6*m^2 + quadraticGap eg em +
        (-g)*(2*eg+9*em) + 3*(g+3*m)*(eg+5*em) := by
  unfold quadraticGap
  ring

theorem quadratic_cross_nonneg (g m b d : Int)
    (hm : 0 ≤ m) (hsep : 0 < g+3*m)
    (h1 : 0 ≤ 2*b+d) (h2 : 0 ≤ b+d) (h3 : 0 ≤ b+2*d) :
    0 ≤ g*(2*b+d)+9*m*(b+d) := by
  by_cases hg : 0 ≤ g
  · have hm' : 0 ≤ 9*m := by positivity
    exact add_nonneg (mul_nonneg hg h1) (mul_nonneg hm' h2)
  · have hrel : 2*b+d ≤ 3*(b+d) := by omega
    have hmul : g*(3*(b+d)) ≤ g*(2*b+d) :=
      mul_le_mul_of_nonpos_left hrel (by omega)
    have hprod : 0 ≤ 3*(g+3*m)*(b+d) := by positivity
    nlinarith

/-- Exact source correction cone implies quadratic growth for either output
side. The proof does not assume that the leading branch matches the sign of g. -/
theorem quadratic_gap_scale_gain (m c v u B E : Nat) (g : Int)
    (hgap : g = (u : Int)+(c : Int)+(v : Int)-3*(m : Int))
    (hm : 0 ≤ (m : Int))
    (hsep : 0 < g+3*(m : Int))
    (h1 : 0 ≤ 2*beta B c v + delta E m)
    (h2 : 0 ≤ beta B c v + delta E m)
    (h3 : 0 ≤ beta B c v + 2*delta E m) :
    quadraticGap (gap (B+u) E) (scale (B+u) E : Int) ≥
      quadraticGap g (m : Int)+6*(m : Int)^2 := by
  by_cases hleft : E ≤ B+u
  · obtain ⟨hg',hm'⟩ := left_update m c v u B E g hgap hleft
    let eg : Int := beta B c v - 4*delta E m
    let em : Int := delta E m
    have hqerr := quadraticGap_nonneg eg em
    have hcross := quadratic_cross_nonneg g (m : Int)
      (beta B c v) (delta E m) hm hsep h1 h2 h3
    calc
      quadraticGap (gap (B+u) E) (scale (B+u) E : Int) =
          quadraticGap (g-9*(m : Int)+eg) (3*(m : Int)+em) := by
            rw [hg',hm']
            simp [eg,em]
      _ = quadraticGap g (m : Int)+6*(m : Int)^2+
            quadraticGap eg em+
            g*(2*beta B c v+delta E m)+
            9*(m : Int)*(beta B c v+delta E m) := by
              rw [quadraticGap_left_expansion]
              simp [eg,em]
      _ ≥ quadraticGap g (m : Int)+6*(m : Int)^2 := by
            nlinarith
  · have hright : B+u < E := by omega
    obtain ⟨hg',hm'⟩ := right_update m c v u B E g hgap hright
    let eg : Int := delta E m - 4*beta B c v
    let em : Int := beta B c v
    have hqerr := quadraticGap_nonneg eg em
    have hcross := quadratic_cross_nonneg g (m : Int)
      (beta B c v) (delta E m) hm hsep h1 h2 h3
    calc
      quadraticGap (gap (B+u) E) (scale (B+u) E : Int) =
          quadraticGap (-4*g-9*(m : Int)+eg)
            (3*(m : Int)+g+em) := by
              rw [hg',hm']
              simp [eg,em]
      _ = quadraticGap g (m : Int)+6*(m : Int)^2+
            quadraticGap eg em+
            g*(2*beta B c v+delta E m)+
            9*(m : Int)*(beta B c v+delta E m) := by
              rw [quadraticGap_right_expansion]
              simp [eg,em]
              ring
      _ ≥ quadraticGap g (m : Int)+6*(m : Int)^2 := by
            nlinarith

/-- Extract the exact B-drain from a left-odd canonical base transition. -/
theorem leftOddBaseDrain (d k B E : Nat) (hd : d%2=1)
    (hbase : highLevelNext (.D (d+5+k) d) = some (.D B E)) :
    drainB k (d+3) 5 = some (.D B E) := by
  have hEq : highLevelNext (.D (d+5+k) d) = drainB k (d+3) 5 := by
    rw [highLevelNext]
    have h0 : d+5+k ≠ 0 := by omega
    have h1 : d%2=1 ∧ d+5+k≥d+5 := by omega
    simp only [if_neg h0, if_pos h1]
    have harg : d+5+k-d-5=k := by omega
    rw [harg]
  rw [hEq] at hbase
  exact hbase

/-- Extract the exact B-drain from a left-even canonical base transition. -/
theorem leftEvenBaseDrain (d k B E : Nat) (hd : d%2=0)
    (hbase : highLevelNext (.D (d+2+k) d) = some (.D B E)) :
    drainB k (d+2) 2 = some (.D B E) := by
  have hEq : highLevelNext (.D (d+2+k) d) = drainB k (d+2) 2 := by
    rw [highLevelNext]
    have h0 : d+2+k ≠ 0 := by omega
    have h1neg : ¬(d%2=1 ∧ d+2+k≥d+5) := by omega
    have h1pos : d%2=0 ∧ d+2+k≥d+3 := by omega
    simp only [if_neg h0, if_neg h1neg, if_pos h1pos]
    have harg : d+2+k-d-2=k := by omega
    rw [harg]
  rw [hEq] at hbase
  exact hbase

/-- Extract the exact B-drain from a right-odd canonical base transition. -/
theorem rightOddBaseDrain (a k B E : Nat) (ha : 0<a) (he : a%2=0)
    (hbase : highLevelNext (.D a (a+1+2*k)) = some (.D B E)) :
    drainB (2*k+5) (a-1) 3 = some (.D B E) := by
  have hEq : highLevelNext (.D a (a+1+2*k)) =
      drainB (2*k+5) (a-1) 3 := by
    rw [highLevelNext]
    have h0 : a ≠ 0 := by omega
    have h1 : ¬((a+1+2*k)%2=1 ∧ a≥a+1+2*k+5) := by omega
    have h2 : ¬((a+1+2*k)%2=0 ∧ a≥a+1+2*k+3) := by omega
    have hodd : a%2 ≠ 1 := by omega
    have heq : a ≠ a+1+2*k+2 := by omega
    have hdBase : (a+1+2*k)%2=1 := by omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg hodd, if_neg heq, if_pos hdBase]
    have harg : a+1+2*k+4-a=2*k+5 := by omega
    rw [harg]
  rw [hEq] at hbase
  exact hbase

/-- Extract the evaluator and complete drain from a right-even canonical base. -/
theorem rightEvenBaseEvalDrain (a k B E : Nat) (ha : 0<a) (he : a%2=0)
    (hbase : highLevelNext (.D a (a+2+2*k)) = some (.D B E)) :
    ∃ a1 b1 d1,
      evalA (2*k+3) a (2*a+5) = some (a1,b1,d1) ∧
      drainB a1 b1 d1 = some (.D B E) := by
  have hEq : highLevelNext (.D a (a+2+2*k)) =
      (evalA (2*k+3) a (2*a+5)).bind
        (fun p => drainB p.1 p.2.1 p.2.2) := by
    rw [highLevelNext]
    have h0 : a ≠ 0 := by omega
    have h1neg : ¬((a+2+2*k)%2=1 ∧ a≥a+2+2*k+5) := by omega
    have h2neg : ¬((a+2+2*k)%2=0 ∧ a≥a+2+2*k+3) := by omega
    have hodd : a%2 ≠ 1 := by omega
    have heq : a ≠ a+2+2*k+2 := by omega
    have hdBaseNotOne : (a+2+2*k)%2 ≠ 1 := by omega
    simp only [if_neg h0, if_neg h1neg, if_neg h2neg, if_neg hodd, if_neg heq, if_neg hdBaseNotOne]
    have harg : a+2+2*k+1-a=2*k+3 := by omega
    rw [harg]
  rw [hEq] at hbase
  cases heval : evalA (2*k+3) a (2*a+5) with
  | none =>
      simp [heval] at hbase
  | some p =>
      rcases p with ⟨a1,b1,d1⟩
      simp only [heval,Option.bind_some] at hbase
      exact ⟨a1,b1,d1,heval,hbase⟩

/-- Every successful transition in the four-sector canonical cone strictly
increases the common quadratic gap potential by at least six times the
square of the smaller counter. -/
theorem newAffine_quadratic_gain (a d : Nat)
    (hcone : newAffineCone a d) :
    ∃ a' d',
      highLevelNext (.D a d) = some (.D a' d') ∧
      quadraticGap (gap a' d') (scale a' d' : Int) ≥
        quadraticGap (gap a d) (scale a d : Int)+6*(scale a d : Int)^2 := by
  rcases hcone with hLO | hLE | hRO | hRE
  · rcases hLO with ⟨hd,hbranch,hbudget⟩
    let k := leftOddExponent d
    let t := a-d-5-k
    have hk : k ≤ a-d-5 := by
      dsimp [k]
      exact leftOddExponent_le d (a-d-5) hbudget
    have hdecomp : a=d+5+k+t := by dsimp [t]; omega
    obtain ⟨B,E,hactual,hbase⟩ :=
      leftOddCanonicalTransition a d hd hbranch hbudget
    have hbase' : highLevelNext (.D (d+5+k) d) = some (.D B E) := by
      simpa [k] using hbase
    have hdrain := leftOddBaseDrain d k B E hd hbase'
    have hres := left_odd_residual_bounds k d B E
      (by simpa [k] using leftOddExponent_spec d) hdrain
    have hm : scale a d = d := by
      simp [scale,Nat.min_eq_right (by omega : d≤a)]
    have hg : gap a d = (a:Int)-4*(d:Int) := by
      simp [gap, Nat.not_lt_of_ge (by omega : d≤a)]
    have hgap : gap a d = (t:Int)+5+(k:Int)-3*(scale a d:Int) := by
      rw [hg,hm]
      dsimp [t]
      omega
    have hsep : 0 < gap a d+3*(scale a d:Int) := by
      rw [hg,hm]
      omega
    have hactual' : highLevelNext (.D a d) = some (.D (B+t) E) := by
      simpa [k,t] using hactual
    have hgain := quadratic_gap_scale_gain d 5 k t B E (gap a d)
      hgap (by positivity) hsep
      (by omega) (by omega) (by omega)
    exact ⟨B+t,E,hactual',by simpa [hm] using hgain⟩
  · rcases hLE with ⟨hd,hbranch,hbudget⟩
    let k := leftEvenExponent d
    let t := a-d-2-k
    have hk : k ≤ a-d-2 := by
      dsimp [k]
      exact leftEvenExponent_le d (a-d-2) hbudget
    have hdecomp : a=d+2+k+t := by dsimp [t]; omega
    obtain ⟨B,E,hactual,hbase⟩ :=
      leftEvenCanonicalTransition a d hd hbranch hbudget
    have hbase' : highLevelNext (.D (d+2+k) d) = some (.D B E) := by
      simpa [k] using hbase
    have hdrain := leftEvenBaseDrain d k B E hd hbase'
    have hres := left_even_residual_bounds k d B E
      (by simpa [k] using leftEvenExponent_spec d) hdrain
    have hm : scale a d = d := by
      simp [scale,Nat.min_eq_right (by omega : d≤a)]
    have hg : gap a d = (a:Int)-4*(d:Int) := by
      simp [gap, Nat.not_lt_of_ge (by omega : d≤a)]
    have hgap : gap a d = (t:Int)+2+(k:Int)-3*(scale a d:Int) := by
      rw [hg,hm]
      dsimp [t]
      omega
    have hsep : 0 < gap a d+3*(scale a d:Int) := by
      rw [hg,hm]
      omega
    have hactual' : highLevelNext (.D a d) = some (.D (B+t) E) := by
      simpa [k,t] using hactual
    have hgain := quadratic_gap_scale_gain d 2 k t B E (gap a d)
      hgap (by positivity) hsep
      (by omega) (by omega) (by omega)
    exact ⟨B+t,E,hactual',by simpa [hm] using hgain⟩
  · rcases hRO with ⟨ha,he,hside,hd,hbudget⟩
    let k := rightOddExponent a
    let q := (d-a-1)/2
    let t := q-k
    have hbudgetQ : a-1 ≤ ternaryOnes (2*q+5) := by
      have harg : 2*q+5=d+4-a := by dsimp [q]; omega
      rw [harg]
      exact hbudget
    have hk : k≤q := by
      dsimp [k]
      exact rightOddExponent_le a q hbudgetQ
    have hdecomp : d=a+1+2*k+2*t := by dsimp [t,q]; omega
    obtain ⟨B,E,hactual,hbase⟩ :=
      rightOddCanonicalTransition a d ha he hd hside hbudget
    have hbase' : highLevelNext (.D a (a+1+2*k)) = some (.D B E) := by
      simpa [k] using hbase
    have hdrain := rightOddBaseDrain a k B E ha he hbase'
    have hres := right_odd_residual_bounds k a B E
      (by simpa [k] using rightOddExponent_spec a) hdrain
    have hm : scale a d = a := by
      simp [scale,Nat.min_eq_left (by omega : a≤d)]
    have hg : gap a d = (d:Int)-4*(a:Int) := by
      simp [gap,Nat.not_le_of_gt (by omega : ¬ d≤a)]
    have hgap : gap a d = 2*(t:Int)+1+2*(k:Int)-3*(scale a d:Int) := by
      rw [hg,hm]
      dsimp [t,q]
      omega
    have hsep : 0 < gap a d+3*(scale a d:Int) := by
      rw [hg,hm]
      omega
    have hactual' : highLevelNext (.D a d) = some (.D (B+2*t) E) := by
      simpa [k,q,t] using hactual
    have hgain := quadratic_gap_scale_gain a 1 (2*k) (2*t) B E (gap a d)
      hgap (by positivity) hsep
      (by omega) (by omega) (by omega)
    exact ⟨B+2*t,E,hactual',by simpa [hm] using hgain⟩
  · rcases hRE with ⟨ha,he,hside,hd,hbudget⟩
    let k := rightEvenExponent a
    let q := d/2-a/2-1
    let t := q-k
    have hbudgetQ : a < ternaryOnes (2*q+3) := by
      have harg : 2*q+3=d+1-a := by dsimp [q]; omega
      rw [harg]
      exact hbudget
    have hk : k≤q := by
      dsimp [k]
      exact rightEvenExponent_le a q hbudgetQ
    have hdecomp : d=a+2+2*k+2*t := by dsimp [t,q]; omega
    obtain ⟨B,E,hactual,hbase⟩ :=
      rightEvenCanonicalTransition a d ha he hd hside hbudget
    have hbase' : highLevelNext (.D a (a+2+2*k)) = some (.D B E) := by
      simpa [k] using hbase
    obtain ⟨a1,b1,d1,hEval,hDrain⟩ := rightEvenBaseEvalDrain a k B E ha he hbase'
    have hres := right_even_residual_bounds k a a1 b1 d1 B E
      (by simpa [k] using rightEvenExponent_spec a) hEval hDrain
    have hm : scale a d = a := by
      simp [scale,Nat.min_eq_left (by omega : a≤d)]
    have hg : gap a d = (d:Int)-4*(a:Int) := by
      simp [gap,Nat.not_le_of_gt (by omega : ¬ d≤a)]
    have hgap : gap a d = 2*(t:Int)+2+2*(k:Int)-3*(scale a d:Int) := by
      rw [hg,hm]
      dsimp [t,q]
      omega
    have hsep : 0 < gap a d+3*(scale a d:Int) := by
      rw [hg,hm]
      omega
    have hactual' : highLevelNext (.D a d) = some (.D (B+2*t) E) := by
      simpa [k,q,t] using hactual
    have hgain := quadratic_gap_scale_gain a 2 (2*k) (2*t) B E (gap a d)
      hgap (by positivity) hsep
      (by omega) (by omega) (by omega)
    exact ⟨B+2*t,E,hactual',by simpa [hm] using hgain⟩

#print axioms drainB_first_le_iter
#print axioms left_odd_residual_bounds
#print axioms left_even_residual_bounds
#print axioms right_odd_residual_bounds
#print axioms right_even_residual_bounds
#print axioms quadratic_gap_scale_gain
#print axioms newAffine_quadratic_gain

end BB6.Agent49GapScaleResidualSource
