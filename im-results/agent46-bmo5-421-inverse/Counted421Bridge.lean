import Counted421
import Cap

namespace Counted421

theorem eval_next {w v : Work} {fuel cost : Nat} (h : macroStep w=(cost,.inl v)) :
    (eval (fuel+1) w).2=(eval fuel v).2 := by simp [eval,h]

theorem eval_done {w : Work} {x : Option Nat} {fuel cost : Nat} (h : macroStep w=(cost,.inr x)) :
    (eval (fuel+1) w).2=x := by simp [eval,h]

theorem eval_c2 (a b fuel : Nat) (hf : a+1≤fuel) :
    (eval fuel (.c2 a b)).2=some (2*(a+b)+7) := by
  induction a using Nat.strongRecOn generalizing b fuel with
  | ind a ih =>
    obtain ⟨n,rfl⟩ : ∃ n, fuel=n+1 := ⟨fuel-1,by omega⟩
    rcases a with _|_|a
    · simp [eval,macroStep]
    · simp [eval,macroStep]; omega
    · rw [eval_next (show macroStep (.c2 (a+2) b)=(4*b+14,.inl (.c2 a (b+2))) by rfl)]
      rw [ih a (by omega) (b+2) n (by omega)]
      congr 1 <;> omega

/-- Exact diagonal drain, retaining the unused evaluator fuel. -/
theorem eval_strip (n a r c fuel : Nat) :
    (eval (n+fuel) (.d a (2*(r+n)+1) (c+n))).2=
      (eval fuel (.d (a+2*n) (2*r+1) c)).2 := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [show n+1+fuel=n+fuel+1 by omega,show 2*(r+(n+1))+1=(2*(r+n)+1)+2 by omega,
      show c+(n+1)=c+n+1 by omega]
    rw [eval_next (show macroStep (.d a ((2*(r+n)+1)+2) (c+n+1))=(4*a+8,.inl (.d (a+2) (2*(r+n)+1) (c+n))) by exact macroStep.eq_13 _ _ _)]
    rw [ih (a+2),show a+2+2*n=a+2*(n+1) by omega]

/-- The counted section and the prior unweighted half-counter recurrence agree. -/
theorem eval_d_odd (r c fuel : Nat) (hf : 6*r+10≤fuel) :
    (eval fuel (.d 0 (2*r+1) c)).2=(Cap.drain r c).map Cap.oddCounter := by
  induction r using Nat.strongRecOn generalizing c fuel with
  | ind r ih =>
    rw [Cap.drain]
    by_cases h : r≤c
    · rw [ite_eq_left h]
      let n := fuel-r-2
      have hfu : fuel=r+(n+2) := by dsimp [n]; omega
      have hstrip := eval_strip r 0 0 (c-r) (n+2)
      simp only [Nat.zero_add,Nat.mul_zero] at hstrip
      rw [show c-r+r=c by omega,←hfu] at hstrip
      rw [hstrip]
      by_cases hc : c=r
      · rw [show c-r=0 by omega]
        rw [show n+2=n+1+1 by omega,eval_next (show macroStep (.d (2*r) 1 0)=(8*(2*r)+26,.inl (.c2 (2*(2*r)+3) 0)) by rfl)]
        rw [eval_c2 _ _ _ (by dsimp [n]; omega)]
        simp [Cap.oddCounter]; omega
      · obtain ⟨z,hz⟩ : ∃ z, c-r=z+1 := ⟨c-r-1,by omega⟩
        rw [hz,show n+2=n+1+1 by omega,
          eval_next (show macroStep (.d (2*r) 1 (z+1))=(4*(2*r)+8,.inl (.d (2*r+1) 0 z)) by rfl)]
        cases z with
        | zero =>
          rw [eval_next (show macroStep (.d (2*r+1) 0 0)=(4*(2*r+1)+18,.inl (.c2 (2*(2*r+1)+1) 1)) by rfl)]
          rw [eval_c2 _ _ _ (by dsimp [n]; omega)]
          simp [Cap.oddCounter]; omega
        | succ z =>
          rw [eval_next (show macroStep (.d (2*r+1) 0 (z+1))=(4*(2*r+1)+8,.inl (.c2 (2*(2*r+1)+3) z)) by rfl)]
          rw [eval_c2 _ _ _ (by dsimp [n]; omega)]
          simp [Cap.oddCounter]; omega
    · rw [ite_eq_right h]
      let n := fuel-c-1
      have hfu : fuel=c+(n+1) := by dsimp [n]; omega
      have hstrip := eval_strip c 0 (r-c) 0 (n+1)
      simp only [Nat.zero_add] at hstrip
      rw [show r-c+c=r by omega,←hfu] at hstrip
      rw [hstrip]
      by_cases h1 : r=c+1
      · rw [ite_eq_left h1,show 2*(r-c)+1=3 by omega]
        exact eval_done (by rfl : macroStep (.d (2*c) 3 0)=(10*(2*c)+33,.inr none))
      · rw [ite_eq_right h1]
        by_cases h2 : r=c+2
        · rw [ite_eq_left h2,show 2*(r-c)+1=5 by omega]
          rw [eval_next (show macroStep (.d (2*c) 5 0)=(10*(2*c)+38,.inl (.c2 1 (2*c+3))) by rfl)]
          rw [eval_c2 _ _ _ (by dsimp [n]; omega)]
          simp [Cap.oddCounter]; omega
        · rw [ite_eq_right h2,show 2*(r-c)+1=2*(r-c-3)+1+6 by omega]
          rw [eval_next (show macroStep (.d (2*c) (2*(r-c-3)+1+6) 0)=(10*(2*c)+34,.inl (.d 0 (2*(r-c-3)+1) (2*c+4))) by rfl)]
          exact ih _ (by omega) _ _ (by dsimp [n]; omega)

theorem section_f (x : Nat) (hx : 0<x) :
    (sectionEval (Cap.oddCounter x)).2=(Cap.f x).map Cap.oddCounter := by
  by_cases h : x=1
  · subst x; decide
  · have ha : Cap.oddCounter x=(2*(x-2)+1)+2 := by simp [Cap.oddCounter]; omega
    rw [ha]
    unfold sectionEval Cap.f
    simp only [show x≠0 by omega,h,ite_false]
    exact eval_d_odd _ _ _ (by omega)

#print axioms eval_d_odd
#print axioms section_f
end Counted421
