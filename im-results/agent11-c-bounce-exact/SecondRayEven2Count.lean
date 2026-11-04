import SecondRayEven2
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Ray
open BB6.Agent46

/-- Separation of the additional boundary input from all old fan sources. -/
theorem even2Boundary_ne_fan (s t:Nat) :
 even2Boundary (s+t+1)≠(FanArithmetic.p s t,FanArithmetic.q s t) := by
  intro h
  let m:=s+t+1
  have hp : FanArithmetic.p s t+3=4*FanArithmetic.a s t := by
    have hb:=(FanArithmetic.bounds s t).2.2.2.2
    unfold FanArithmetic.p at hb ⊢
    omega
  have hB:FanArithmetic.b s t=3*m+4 := by
    dsimp [FanArithmetic.b,FanArithmetic.m,m]
  have hA : 3*m+4≤FanArithmetic.a s t := by
    rw [FanArithmetic.a,hB]
    have hpow:1≤4^t := Nat.one_le_pow t 4 (by decide)
    have hh:=Nat.mul_le_mul_right (3*m+4) hpow
    simpa using hh
  have hfirst:=congrArg Prod.fst h
  dsimp [even2Boundary,m] at hfirst
  omega

theorem even2Boundary_ne_direct (m:Nat) :
 even2Boundary m≠oddRayDirect m := by
  intro h
  have hf:=rayFacts m
  have hD: 6*m+16≤rayD m := by omega
  have hfirst:=congrArg Prod.fst h
  dsimp [even2Boundary,oddRayDirect] at hfirst
  omega

/-- The additional boundary input is separate from all m+1 previously
    indexed direct/fan entries, for every m. -/
theorem even2Boundary_ne_oddRayIndexed (m:Nat) (i:Fin (m+1)) :
 even2Boundary m≠oddRayIndexed m i := by
  cases i using Fin.cases with
  | zero =>
      simpa only [oddRayIndexed,Fin.cases_zero] using even2Boundary_ne_direct m
  | succ i =>
      have hs:i.val<m := i.isLt
      have ht:m=i.val+(m-i.val-1)+1 := by omega
      have hb:=even2Boundary_ne_fan i.val (m-i.val-1)
      have hEq : i.val+(m-i.val-1)+1=m := by omega
      rw [hEq] at hb
      simpa only [oddRayIndexed,Fin.cases_succ,FanArithmetic.source] using hb

/-- All-parameter direct-or-fan source indexing, independent of
    whether the target parameter is odd or even. -/
theorem oddRayIndexed_shape (m a k:Nat) :
  ((a,k)=oddRayDirect m ∨
    ∃ s t:Nat, m=s+t+1 ∧ a=FanArithmetic.p s t ∧ k=FanArithmetic.q s t) ↔
    ∃ i:Fin (m+1), oddRayIndexed m i=(a,k) := by
  constructor
  · rintro (hd | ⟨s,t,hst,ha,hk⟩)
    · refine ⟨0,?_⟩
      simpa only [oddRayIndexed,Fin.cases_zero] using hd.symm
    · have hs:s<m:=by omega
      let i:Fin m:=⟨s,hs⟩
      have ht:t=m-s-1:=by omega
      refine ⟨Fin.succ i,?_⟩
      simp only [oddRayIndexed,Fin.cases_succ]
      change (FanArithmetic.p s (m-s-1),FanArithmetic.q s (m-s-1))=(a,k)
      rw [←ht,←ha,←hk]
  · rintro ⟨i,hi⟩
    cases i using Fin.cases with
    | zero =>
        exact Or.inl (by simpa only [oddRayIndexed,Fin.cases_zero] using hi.symm)
    | succ i =>
        right
        let s:=i.val
        let t:=m-i.val-1
        have hst:m=s+t+1:=by dsimp [s,t];have hs:=i.isLt;omega
        have heq:(FanArithmetic.p s t,FanArithmetic.q s t)=(a,k) := by
          simpa only [oddRayIndexed,Fin.cases_succ,FanArithmetic.source] using hi
        exact ⟨s,t,hst,(Prod.mk.inj heq).1.symm,(Prod.mk.inj heq).2.symm⟩

/-- All m+2 inputs of the 2-mod-4 family indexed without duplication. -/
def even2Indexed (m:Nat) : Fin (m+2)→Nat×Nat :=
  Fin.cases (even2Boundary m) (fun i => oddRayIndexed m i)

theorem even2Indexed_injective (m:Nat) : Function.Injective (even2Indexed m) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
          have hneq:=even2Boundary_ne_oddRayIndexed m j
          have heq:even2Boundary m=oddRayIndexed m j := by
            simpa only [even2Indexed,Fin.cases_zero,Fin.cases_succ] using hij
          exact False.elim (hneq heq)
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          have hneq:=even2Boundary_ne_oddRayIndexed m i
          have heq:oddRayIndexed m i=even2Boundary m := by
            simpa only [even2Indexed,Fin.cases_zero,Fin.cases_succ] using hij
          exact False.elim (hneq heq.symm)
      | succ j =>
          have heq:oddRayIndexed m i=oddRayIndexed m j := by
            simpa only [even2Indexed,Fin.cases_succ] using hij
          exact congrArg Fin.succ ((oddRayIndexed_injective m) heq)

/-- Original-source exact cardinality m+2 for every m ≡ 2 (mod 4),
    including all arbitrarily large such halting-family parameters. -/
theorem even2_exact_incoming_count (m:Nat) (hm:m%4=2) :
    ∃ f : Fin (m+2) → Nat×Nat,
    Function.Injective f ∧
      ∀ a k, secNext (a,k)=some (rayX m,rayY m) ↔
        ∃ i:Fin (m+2), f i=(a,k) := by
  refine ⟨even2Indexed m, even2Indexed_injective m,?_⟩
  intro a k
  rw [original_even2_ray_fibre_iff m a k hm]
  constructor
  · rintro (hd | hfan | hboundary)
    · have hdirect : (a,k)=oddRayDirect m := (oddRayDirect_iff m a k).mpr hd
      obtain ⟨i,hi⟩ := (oddRayIndexed_shape m a k).mp (Or.inl hdirect)
      exact ⟨Fin.succ i, by simpa only [even2Indexed,Fin.cases_succ] using hi⟩
    · obtain ⟨i,hi⟩ := (oddRayIndexed_shape m a k).mp (Or.inr hfan)
      exact ⟨Fin.succ i, by simpa only [even2Indexed,Fin.cases_succ] using hi⟩
    · exact ⟨0,by simpa only [even2Indexed,Fin.cases_zero] using hboundary.symm⟩
  · rintro ⟨i,hi⟩
    cases i using Fin.cases with
    | zero =>
        right;right
        simpa only [even2Indexed,Fin.cases_zero] using hi.symm
    | succ i =>
        have hshape:(a,k)=oddRayDirect m ∨
          ∃ s t:Nat, m=s+t+1 ∧ a=FanArithmetic.p s t ∧ k=FanArithmetic.q s t :=
          (oddRayIndexed_shape m a k).mpr
            ⟨i,by simpa only [even2Indexed,Fin.cases_succ] using hi⟩
        rcases hshape with hd | hfan
        · exact Or.inl ((oddRayDirect_iff m a k).mp hd)
        · exact Or.inr (Or.inl hfan)

#print axioms even2Indexed_injective
#print axioms even2_exact_incoming_count
end BB6.Agent11Ray
