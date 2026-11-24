import Counted421Score

namespace Counted421

theorem eval_next_cost {w v : Work} {fuel cost : Nat} (h : macroStep w=(cost,.inl v)) :
    (eval (fuel+1) w).1=cost+(eval fuel v).1 := by simp [eval,h]

theorem eval_done_cost {w : Work} {x : Option Nat} {fuel cost : Nat} (h : macroStep w=(cost,.inr x)) :
    (eval (fuel+1) w).1=cost := by simp [eval,h]

-- Distribute products before omega; all remaining nonlinear monomials coincide.
macro "poly" : tactic => `(tactic| (simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm,Nat.mul_zero,Nat.zero_mul,Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.zero_add] at *; simp only [Nat.reduceMul, ←Nat.mul_assoc] at *; omega))

def c2Cost (t e b : Nat) := 4*t*(b+t)+22*t+6*b+22+4*e

theorem eval_c2_cost (t e b fuel : Nat) (he : e≤1) (hf : 2*t+e+1≤fuel) :
    (eval fuel (.c2 (2*t+e) b)).1=c2Cost t e b := by
  induction t generalizing b fuel with
  | zero =>
    obtain ⟨n,rfl⟩ : ∃ n, fuel=n+1 := ⟨fuel-1,by omega⟩
    rcases e with _|_|e
    · simp [eval,macroStep,c2Cost]
    · simp [eval,macroStep,c2Cost]
    · omega
  | succ t ih =>
    obtain ⟨n,rfl⟩ : ∃ n, fuel=n+1 := ⟨fuel-1,by omega⟩
    rw [show 2*(t+1)+e=(2*t+e)+2 by omega,
      eval_next_cost (show macroStep (.c2 ((2*t+e)+2) b)=(4*b+14,.inl (.c2 (2*t+e) (b+2))) by rfl)]
    rw [ih (b+2) n (by omega)]
    unfold c2Cost
    poly

theorem eval_strip_cost (n a r c fuel : Nat) :
    (eval (n+fuel) (.d a (2*(r+n)+1) (c+n))).1 =
      4*n*(a+n+1)+(eval fuel (.d (a+2*n) (2*r+1) c)).1 := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [show n+1+fuel=n+fuel+1 by omega,show 2*(r+(n+1))+1=(2*(r+n)+1)+2 by omega,
      show c+(n+1)=c+n+1 by omega]
    rw [eval_next_cost (show macroStep (.d a ((2*(r+n)+1)+2) (c+n+1))=(4*a+8,.inl (.d (a+2) (2*(r+n)+1) (c+n))) by exact macroStep.eq_13 _ _ _)]
    rw [ih (a+2),show a+2+2*n=a+2*(n+1) by omega]
    poly

def regularCost (r c : Nat) := 20*r*r+80*r+78+(8*r+14)*(c-r)
def terminalCost (c : Nat) := 4*c*c+24*c+33
def specialCost (c : Nat) := 4*c*c+36*c+82
def resetCost (c : Nat) := 4*c*c+24*c+34

/-- A logarithmic-depth exact weighted drain, avoiding unary iterations. -/
def fastD (r c : Nat) : Nat :=
  if r≤c then regularCost r c
  else if r=c+1 then terminalCost c
  else if r=c+2 then specialCost c
  else resetCost c+fastD (r-c-3) (2*c+4)
termination_by r
decreasing_by omega

theorem eval_d_odd_cost (r c fuel : Nat) (hf : 6*r+10≤fuel) :
    (eval fuel (.d 0 (2*r+1) c)).1=fastD r c := by
  induction r using Nat.strongRecOn generalizing c fuel with
  | ind r ih =>
    rw [fastD]
    by_cases h : r≤c
    · rw [ite_eq_left h]
      let n := fuel-r-2
      have hfu : fuel=r+(n+2) := by dsimp [n]; omega
      have hstrip := eval_strip_cost r 0 0 (c-r) (n+2)
      simp only [Nat.zero_add,Nat.mul_zero] at hstrip
      rw [show c-r+r=c by omega,←hfu] at hstrip
      rw [hstrip]
      by_cases hc : c=r
      · rw [show c-r=0 by omega]
        rw [show n+2=n+1+1 by omega,eval_next_cost (show macroStep (.d (2*r) 1 0)=(8*(2*r)+26,.inl (.c2 (2*(2*r)+3) 0)) by rfl)]
        rw [show 2*(2*r)+3=2*(2*r+1)+1 by omega,eval_c2_cost (2*r+1) 1 0 _ (by decide) (by dsimp [n]; omega)]
        unfold regularCost c2Cost
        rw [show c-r=0 by omega]
        poly
      · obtain ⟨z,hz⟩ : ∃ z, c-r=z+1 := ⟨c-r-1,by omega⟩
        rw [hz,show n+2=n+1+1 by omega,
          eval_next_cost (show macroStep (.d (2*r) 1 (z+1))=(4*(2*r)+8,.inl (.d (2*r+1) 0 z)) by rfl)]
        cases z with
        | zero =>
          rw [eval_next_cost (show macroStep (.d (2*r+1) 0 0)=(4*(2*r+1)+18,.inl (.c2 (2*(2*r+1)+1) 1)) by rfl)]
          rw [show 2*(2*r+1)+1=2*(2*r+1)+1 by rfl,eval_c2_cost (2*r+1) 1 1 _ (by decide) (by dsimp [n]; omega)]
          unfold regularCost c2Cost
          rw [hz]
          poly
        | succ z =>
          rw [eval_next_cost (show macroStep (.d (2*r+1) 0 (z+1))=(4*(2*r+1)+8,.inl (.c2 (2*(2*r+1)+3) z)) by rfl)]
          rw [show 2*(2*r+1)+3=2*(2*r+2)+1 by omega,eval_c2_cost (2*r+2) 1 z _ (by decide) (by dsimp [n]; omega)]
          unfold regularCost c2Cost
          rw [hz]
          poly
    · rw [ite_eq_right h]
      let n := fuel-c-1
      have hfu : fuel=c+(n+1) := by dsimp [n]; omega
      have hstrip := eval_strip_cost c 0 (r-c) 0 (n+1)
      simp only [Nat.zero_add] at hstrip
      rw [show r-c+c=r by omega,←hfu] at hstrip
      rw [hstrip]
      by_cases h1 : r=c+1
      · rw [ite_eq_left h1,show 2*(r-c)+1=3 by omega]
        rw [eval_done_cost (by rfl : macroStep (.d (2*c) 3 0)=(10*(2*c)+33,.inr none))]
        unfold terminalCost
        poly
      · rw [ite_eq_right h1]
        by_cases h2 : r=c+2
        · rw [ite_eq_left h2,show 2*(r-c)+1=5 by omega]
          rw [eval_next_cost (show macroStep (.d (2*c) 5 0)=(10*(2*c)+38,.inl (.c2 1 (2*c+3))) by rfl)]
          rw [show (1:Nat)=2*0+1 by rfl,eval_c2_cost 0 1 (2*c+3) _ (by decide) (by dsimp [n]; omega)]
          unfold c2Cost specialCost
          poly
        · rw [ite_eq_right h2,show 2*(r-c)+1=2*(r-c-3)+1+6 by omega]
          rw [eval_next_cost (show macroStep (.d (2*c) (2*(r-c-3)+1+6) 0)=(10*(2*c)+34,.inl (.d 0 (2*(r-c-3)+1) (2*c+4))) by rfl)]
          rw [ih _ (by omega) _ _ (by dsimp [n]; omega)]
          unfold resetCost
          poly

def fastScore (x : Nat) : Nat := if x=0 then 10 else if x=1 then 39 else 9+fastD (x-2) 1

theorem fastScore_eq (x : Nat) : score x=fastScore x := by
  by_cases h0 : x=0
  · subst x; decide
  by_cases h1 : x=1
  · subst x; decide
  have ha : Cap.oddCounter x=(2*(x-2)+1)+2 := by simp [Cap.oddCounter]; omega
  unfold score fastScore
  rw [ha]
  simp only [h0,h1,ite_false,sectionEval]
  cases he : eval (2*(x-2)+1+2*(2*(x-2)+1)+7) (.d 0 (2*(x-2)+1) 1) with
  | mk n out =>
    have h := eval_d_odd_cost (x-2) 1 (2*(x-2)+1+2*(2*(x-2)+1)+7) (by omega)
    rw [he] at h
    simp only at h
    simp [h]

#print axioms eval_c2_cost
#print axioms eval_strip_cost
#print axioms eval_d_odd_cost
#print axioms fastScore_eq

-- A prefix sum over completed reset bands.
def resetPrefix : Nat → Nat
  | 0 => 0
  | i+1 => resetPrefix i+resetCost (Cap.c i)

theorem fastD_shift_aux (k j r : Nat) :
    resetPrefix k+fastD (Cap.lo (k+j)-Cap.lo k+r) (Cap.c k)=
      resetPrefix (k+j)+fastD r (Cap.c (k+j)) := by
  induction j generalizing k with
  | zero => simp
  | succ j ih =>
    have hle : Cap.lo (k+1)≤Cap.lo (k+(j+1)) := by
      by_cases e : j=0
      · simp [e]
      · exact Nat.le_of_lt (Cap.lo_strict (by omega))
    have hs : Cap.lo (k+(j+1))-Cap.lo k+r≥Cap.c k+3 := by rw [Cap.lo_step] at hle; omega
    rw [fastD]
    simp only [show ¬ Cap.lo (k+(j+1))-Cap.lo k+r≤Cap.c k by omega,ite_false,
      show Cap.lo (k+(j+1))-Cap.lo k+r≠Cap.c k+1 by omega,
      show Cap.lo (k+(j+1))-Cap.lo k+r≠Cap.c k+2 by omega]
    have he : Cap.lo (k+(j+1))-Cap.lo k+r-Cap.c k-3=Cap.lo ((k+1)+j)-Cap.lo (k+1)+r := by
      rw [show k+(j+1)=(k+1)+j by omega] at *
      rw [Cap.lo_step] at hle
      rw [Cap.lo_step]
      omega
    rw [he,←Cap.c_succ,←Nat.add_assoc,←resetPrefix,ih (k+1),show k+1+j=k+(j+1) by omega]

theorem fastD_shift (i r : Nat) : fastD (Cap.lo i-2+r) 1=resetPrefix i+fastD r (Cap.c i) := by
  have h := fastD_shift_aux 0 i r
  simpa [resetPrefix,Cap.lo,Cap.c] using h

theorem score_band (i r : Nat) : score (Cap.lo i+r)=9+resetPrefix i+fastD r (Cap.c i) := by
  have h := Cap.lo_ge i
  rw [fastScore_eq]
  unfold fastScore
  simp only [show Cap.lo i+r≠0 by omega,show Cap.lo i+r≠1 by omega,ite_false]
  rw [show Cap.lo i+r-2=Cap.lo i-2+r by omega,fastD_shift]
  omega

theorem score_regular (i r : Nat) (hr : r≤Cap.c i) :
    score (Cap.lo i+r)=9+resetPrefix i+regularCost r (Cap.c i) := by
  rw [score_band,fastD,ite_eq_left hr]

theorem score_terminal (i : Nat) : score (Cap.halt i)=resetPrefix (i+1)+8 := by
  unfold Cap.halt
  rw [show Cap.lo i+Cap.c i+1=Cap.lo i+(Cap.c i+1) by omega,score_band,fastD]
  simp only [show ¬Cap.c i+1≤Cap.c i by omega,ite_false,ite_true,resetPrefix]
  unfold terminalCost resetCost
  omega

theorem score_special (i : Nat) : score (Cap.special i)=resetPrefix (i+1)+12*Cap.c i+57 := by
  unfold Cap.special
  rw [show Cap.lo i+Cap.c i+2=Cap.lo i+(Cap.c i+2) by omega,score_band,fastD]
  simp only [show ¬Cap.c i+2≤Cap.c i by omega,ite_false,show Cap.c i+2≠Cap.c i+1 by omega,ite_true,resetPrefix]
  unfold specialCost resetCost
  omega

theorem resetCost_band (i : Nat) : resetCost (Cap.c i)+40*2^i=100*4^i+2 := by
  have h := Cap.c_add i
  have hs : (Cap.c i+4)*(Cap.c i+4)=25*4^i := by
    rw [h]
    calc
      5*2^i*(5*2^i)=25*(2^i*2^i) := by calc
        5*2^i*(5*2^i) = (5*5)*(2^i*2^i) := by ac_rfl
        _ = _ := rfl
      _ = _ := by rw [←Nat.mul_pow]
  unfold resetCost
  poly

theorem resetPrefix_closed (i : Nat) : 3*resetPrefix i+120*2^i=100*4^i+20+6*i := by
  induction i with
  | zero => decide
  | succ i ih =>
    rw [resetPrefix,Nat.pow_succ,Nat.pow_succ]
    have h := resetCost_band i
    omega

#print axioms score_regular
#print axioms score_terminal
#print axioms score_special
#print axioms resetPrefix_closed
end Counted421
