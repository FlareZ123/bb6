import DensityOneExtension
import SourceCounter
import Barrier
import Lean.Elab.Tactic.Omega

namespace BB6.Agent31F321Density

/-- Exact reverse source-map path of length n from (A,D) to (X,Y). -/
inductive BackwardRun : Nat → Nat → Nat → Nat → Nat → Prop where
  | nil (A D : Nat) : BackwardRun 0 A D A D
  | step {n A D a b X Y : Nat}
       (h : CounterMove a b A D)
       (tail : BackwardRun n a b X Y) :
       BackwardRun (n+1) A D X Y

/-- Transport a source-counter inverse path through the large-second
    barrier into the generic all-length formal H/F word certificate. -/
theorem backward_to_formal (seed : Int) (w0 : List InverseLetter)
   {n A D X Y : Nat}
   (hp : FormalInversePath seed w0 (A:Int) (D:Int))
   (hr : BackwardRun n A D X Y)
   (hb : 6*2^n ≤ D+3) :
    ∃ w : List InverseLetter,
     FormalInversePath seed w (X:Int) (Y:Int) ∧ w.length = w0.length+n := by
  induction hr generalizing seed w0 with
  | nil A D =>
      exact ⟨w0,hp,by simp⟩
  | @step n A D a b X Y h tail ih =>
      have hbLarge : 3 ≤ D := big_implies_large (n+1) D hb
      rcases high_far_integral_equations h hbLarge with he | hf
      · have hp' : FormalInversePath seed (.high::w0) (a:Int) (b:Int) :=
          FormalInversePath.stepH hp he.1 he.2
        have hb' : 6*2^n ≤ b+3 := by
          have hD : D = 2*b+3 := by omega
          exact big_next_high n D b hb hD
        obtain ⟨w, hw, hlen⟩ := ih seed (.high::w0) hp' hb'
        exact ⟨w,hw,by simp at hlen; omega⟩
      · have hp' : FormalInversePath seed (.far::w0) (a:Int) (b:Int) :=
          FormalInversePath.stepF hp hf.1 hf.2
        have hb' : 6*2^n ≤ b+3 := by
          have hD : D ≤ b := by
            rcases large_second_only_high_far h hbLarge with hh | hf'
            · omega
            · omega
          exact big_next_far n D b hb hD
        obtain ⟨w, hw, hlen⟩ := ih seed (.far::w0) hp' hb'
        exact ⟨w,hw,by simp at hlen; omega⟩

/-- Every bounded-length inverse path whose entry has a sufficiently large
    second counter remains above 2 throughout. -/
theorem backward_end_large
   {n A D X Y : Nat} (hr : BackwardRun n A D X Y)
   (hb : 6*2^n ≤ D+3) : 3 ≤ Y := by
  induction hr with
  | nil A D => exact big_implies_large 0 D hb
  | @step n A D a b X Y h tail ih =>
      have hLarge : 3 ≤ D := big_implies_large (n+1) D hb
      rcases large_second_only_high_far h hLarge with hh | hf
      · have hb' : 6*2^n ≤ b+3 :=
          big_next_high n D b hb hh.2
        exact ih hb'
      · have hb' : 6*2^n ≤ b+3 := by
          have hDb : D ≤ b := by omega
          exact big_next_far n D b hb hDb
        exact ih hb'

/-- Every finite backward path has a prefix of any shorter length. -/
theorem backward_take (n : Nat) {m A D X Y:Nat}
   (hr : BackwardRun m A D X Y) (hLen:n≤m) :
    ∃ x y, BackwardRun n A D x y := by
  induction hr generalizing n with
  | nil A D =>
      have hn : n=0 := by omega
      subst n
      exact ⟨A,D,BackwardRun.nil A D⟩
  | @step m A D a b X Y h tail ih =>
      cases n with
      | zero => exact ⟨A,D,BackwardRun.nil A D⟩
      | succ n =>
          have hle:n≤m := by omega
          obtain ⟨x,y,hs⟩ := ih n hle
          exact ⟨x,y,BackwardRun.step h hs⟩

/-- Absence of an integer solution for every formal inverse word at depth n. -/
def NoIntegralWord (n d:Nat) : Prop :=
  ∀ w:List InverseLetter, w.length=n →
    ∀ A:Int, (2:Int)^(compile w).shift*A ≠
      ((compile w).u:Int)*(d:Int)+(compile w).v

/-- If every integral high/far word at depth n is excluded and the gate
    counter satisfies the explicit growth threshold, the gate cannot have
    the genuine seed (1,1) anywhere in its finite inverse ancestry. -/
theorem no_backward_root (n d:Nat)
  (hb:6*2^n≤d+3)
  (hn:NoIntegralWord n d) :
    ∀ m, ¬BackwardRun m (d+1) d 1 1 := by
  intro m hr
  by_cases hlen:m≤n
  · have hbSmaller:6*2^m≤d+3 := by
      have hpow:2^m≤2^n := Nat.pow_le_pow_right (by decide : 0<2) hlen
      omega
    have hy:=backward_end_large hr hbSmaller
    omega
  · have hle:n≤m := by omega
    obtain ⟨x,y,hrn⟩ := backward_take n hr hle
    have hp0:FormalInversePath (d:Int) [] ((d+1:Int)) (d:Int) :=
      FormalInversePath.nil
    obtain ⟨w,hw,hlenw⟩ := backward_to_formal (d:Int) [] hp0 hrn hb
    have heq := (formal_inverse_congruence hw).1
    have hno := hn w (by simpa using hlenw) (x:Int)
    exact hno heq

/-- Conventional finite forward orbit on the exact published F321 map. -/
inductive CounterReach (seedA seedD:Nat) : Nat → Nat → Nat → Prop where
  | nil : CounterReach seedA seedD 0 seedA seedD
  | step {n a d A D:Nat}
      (hr:CounterReach seedA seedD n a d)
      (h:CounterMove a d A D) :
      CounterReach seedA seedD (n+1) A D

theorem reach_to_backward {seedA seedD n A D:Nat}
    (hr:CounterReach seedA seedD n A D) :
    BackwardRun n A D seedA seedD := by
  induction hr with
  | nil => exact BackwardRun.nil _ _
  | step hr h ih => exact BackwardRun.step h ih

def NoResidueWord (n d:Nat) : Prop :=
  ∀ w:List InverseLetter, w.length=n →
      (((compile w).u:Int)*(d:Int)+(compile w).v) %
        ((2:Int)^(compile w).shift) ≠ 0

theorem no_residue_implies_no_integral (n d:Nat)
    (hr:NoResidueWord n d) : NoIntegralWord n d := by
  intro w hw A heq
  have hno := hr w hw
  apply hno
  rw [← heq]
  simp

/-- Full source-counter reachability conclusion. Passing a *finite*
    depth-n congruence test eliminates all forward paths of arbitrary
    length from the genuine (1,1) seed to the d-th halting gate. -/
theorem no_halting_gate_from_seed (n d:Nat)
    (hbound:6*2^n≤d+3)
    (hsieve:NoResidueWord n d) :
    ∀ m, ¬CounterReach 1 1 m (d+1) d := by
  intro m hr
  have inv := reach_to_backward hr
  exact (no_backward_root n d hbound
    (no_residue_implies_no_integral n d hsieve) m) inv

#print axioms no_halting_gate_from_seed
#print axioms backward_to_formal
#print axioms backward_end_large
#print axioms no_backward_root

end BB6.Agent31F321Density
