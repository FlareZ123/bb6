import ExplicitResidueFamilies
import Lean.Elab.Tactic.Omega

namespace BB6.Agent31F321Density

theorem compile_shift_bound (w:List InverseLetter) :
 (compile w).shift ≤ 2*w.length := by
 induction w with
 | nil => decide
 | cons b bs ih =>
   cases b with
   | high => simp only [compile,advance,List.length_cons]; omega
   | far => simp only [compile,advance,List.length_cons]; omega

private theorem linear_mod_period (u v:Int) (s n d k:Nat)
    (h:s≤2*n) :
    (u*((d+2^(2*n)*k):Int)+v)%((2:Int)^s) =
    (u*(d:Int)+v)%((2:Int)^s) := by
  obtain ⟨factor,hfact⟩ := Nat.pow_dvd_pow 2 h
  have hInt : ((2:Int)^(2*n)) = ((2:Int)^s)*(factor:Int) := by
    exact_mod_cast hfact
  rw [hInt]
  have heq : u*((d:Int)+(((2:Int)^s)*(factor:Int))*(k:Int))+v =
      (u*(d:Int)+v) + ((2:Int)^s)*(u*(factor:Int)*(k:Int)) := by
    rw [Int.mul_add]
    ac_rfl
  rw [heq]
  exact Int.add_mul_emod_self_left _ _ _

private theorem all_eq_of_mem_eq {α:Type} (l:List α) (p q:α→Bool)
    (h:∀x∈l,p x=q x): l.all p=l.all q := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      have ha:p a=q a := h a (by simp)
      have ht:∀x∈as,p x=q x := by
        intro x hx
        exact h x (by simp [hx])
      simp only [List.all_cons, ha, ih ht]

theorem words_length (n:Nat) (w:List InverseLetter) (h:w∈words n) :
    w.length=n := by
  induction n generalizing w with
  | zero =>
      simp [words] at h
      subst w
      rfl
  | succ n ih =>
      simp only [words, List.mem_append, List.mem_map] at h
      rcases h with ⟨v,hv,hEq⟩ | ⟨v,hv,hEq⟩
      · rw [←hEq]
        simp [ih v hv]
      · rw [←hEq]
        simp [ih v hv]

/-- The finite depth-n modular predicate is exactly periodic with period
    2^(2n); no empirical sampling or floating-point arithmetic. -/
theorem residuePass_periodic (n d k:Nat):
    residuePass n (d+2^(2*n)*k) = residuePass n d := by
  unfold residuePass
  have hpoint : ∀ w∈words n,
      decide ((((compile w).u:Int)*((d+2^(2*n)*k):Int)+ (compile w).v)%
        ((2:Int)^(compile w).shift) ≠ 0) =
      decide ((((compile w).u:Int)*(d:Int)+ (compile w).v)%
        ((2:Int)^(compile w).shift) ≠ 0) := by
    intro w hw
    have hl := words_length n w hw
    have hb : (compile w).shift≤2*n := by
      simpa [hl] using compile_shift_bound w
    have hmod := linear_mod_period (compile w).u (compile w).v
       (compile w).shift n d k hb
    simp only [hmod]
  exact all_eq_of_mem_eq (words n) _ _ hpoint

/-- Each accepted residue r supplies an infinite arithmetic-progression
    exclusion for every genuine seed-to-gate orbit, beyond the cutoff. -/
theorem residue_class_never (n r k:Nat)
    (hr:residuePass n r=true)
    (hb:6*2^n≤r+2^(2*n)*k+3) :
    ∀m, ¬CounterReach 1 1 m
      ((r+2^(2*n)*k)+1) (r+2^(2*n)*k) := by
  apply no_halting_gate_after_decide n (r+2^(2*n)*k) hb
  rw [residuePass_periodic]
  exact hr

/-- Concrete *infinite* kernel-checked residue family,
    including arbitrarily large terminal parameters. -/
theorem gate1000_mod256_never (k:Nat) :
    ∀m, ¬CounterReach 1 1 m (1001+256*k) (1000+256*k) := by
  have hbase := residue_class_never 4 1000 k (by decide) (by simp; omega)
  intro m hm
  apply hbase m
  have hEq : 1000 + 256*k + 1 = 1001 + 256*k := by omega
  simpa [show 2^(2*4)=256 by decide, hEq] using hm

#print axioms residuePass_periodic
#print axioms residue_class_never
#print axioms gate1000_mod256_never

end BB6.Agent31F321Density
