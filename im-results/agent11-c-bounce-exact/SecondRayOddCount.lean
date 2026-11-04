import SecondRayOddComplete
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Ray
open BB6.Agent46

def oddRayDirect (m:Nat) : Nat×Nat := (rayD m-3,(rayY m-2)/2)
def oddRayIndexed (m:Nat) : Fin (m+1) → Nat×Nat :=
  Fin.cases (oddRayDirect m) (fun i => FanArithmetic.source m i)

theorem oddRayYeven (m:Nat) : (rayY m)%2=0 := by
  have hd : (rayD m)%2=0 := by
    have hfactor : rayD m = 2*(2*(4^m*(3*m+4))) := by
      unfold rayD
      rw [Nat.pow_succ]
      calc
        4^m*4*(3*m+4) = 4*(4^m*(3*m+4)) := by ac_rfl
        _ = 2*(2*(4^m*(3*m+4))) := by omega
    rw [hfactor]
    omega
  have hy := (rayFacts m).2.1
  omega

theorem oddRayDirect_iff (m a k:Nat) :
  (a,k)=oddRayDirect m ↔ a+3=rayD m ∧ 2*k+2=rayY m := by
  have hf:=rayFacts m
  have he:=oddRayYeven m
  have hY: 10≤rayY m := hf.1
  have hD: 3≤rayD m := by omega
  constructor
  · intro h
    have ha : a=rayD m-3 := congrArg Prod.fst h
    have hk : k=(rayY m-2)/2 := congrArg Prod.snd h
    constructor <;> omega
  · rintro ⟨ha,hk⟩
    apply Prod.ext
    · dsimp [oddRayDirect]
      omega
    · dsimp [oddRayDirect]
      omega

/-- In every odd-index ray the exceptional direct input is different
    from all members of the complete high-bounce fan. -/
theorem oddRayDirect_ne_fan (s t : Nat) :
  oddRayDirect (s+t+1) ≠
    (FanArithmetic.p s t,FanArithmetic.q s t) := by
  intro h
  have hp : FanArithmetic.p s t+3=4*FanArithmetic.a s t := by
    have hb := (FanArithmetic.bounds s t).2.2.2.2
    unfold FanArithmetic.p at hb ⊢
    omega
  have hmass := FanArithmetic.d_ge s t
  have hD : FanArithmetic.d s t=rayD (s+t+1) := by
    dsimp [FanArithmetic.d, FanArithmetic.m, FanArithmetic.b,rayD]
  have ha := (oddRayDirect_iff (s+t+1) (FanArithmetic.p s t) (FanArithmetic.q s t)).mp h.symm
  have hApos : 0<FanArithmetic.a s t := by
    unfold FanArithmetic.a
    apply Nat.mul_pos
    · exact Nat.pow_pos (by decide)
    · dsimp [FanArithmetic.b,FanArithmetic.m]
      omega
  omega

/-- The Fin(m+1) source enumeration is injective, so the fibre
    has at least m+1 and no repeated input entries. -/
theorem oddRayIndexed_injective (m:Nat) :
   Function.Injective (oddRayIndexed m) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
          have hneq : oddRayDirect m ≠ FanArithmetic.source m j := by
            have hst : m=j.val+(m-j.val-1)+1 := by have h:=j.isLt;omega
            have hb:=oddRayDirect_ne_fan j.val (m-j.val-1)
            have hEq : j.val+(m-j.val-1)+1=m := by omega
            rw [hEq] at hb
            simpa only [FanArithmetic.source] using hb
          have hf : oddRayDirect m = FanArithmetic.source m j := by
            simpa only [oddRayIndexed,Fin.cases_zero,Fin.cases_succ] using hij
          exact False.elim (hneq hf)
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          have hneq : oddRayDirect m ≠ FanArithmetic.source m i := by
            have hst : m=i.val+(m-i.val-1)+1 := by have h:=i.isLt;omega
            have hb:=oddRayDirect_ne_fan i.val (m-i.val-1)
            have hEq : i.val+(m-i.val-1)+1=m := by omega
            rw [hEq] at hb
            simpa only [FanArithmetic.source] using hb
          have hf : FanArithmetic.source m i = oddRayDirect m := by
            simpa only [oddRayIndexed,Fin.cases_zero,Fin.cases_succ] using hij
          exact False.elim (hneq hf.symm)
      | succ j =>
          have hf : FanArithmetic.source m i=FanArithmetic.source m j := by
            simpa only [oddRayIndexed,Fin.cases_succ] using hij
          have heq:=FanArithmetic.source_injective m hf
          exact congrArg Fin.succ heq

/-- Exhaustiveness: the finite injection enumerates every and only source edge
    of the true original-section odd-parameter second-stopping ray. -/
theorem oddRayIndexed_complete (m a k:Nat) (hm:m%2=1) :
  BB6.Agent46.secNext (a,k)=some (rayX m,rayY m) ↔
    ∃ i : Fin (m+1), oddRayIndexed m i=(a,k) := by
  rw [original_odd_ray_fibre_iff m a k hm]
  constructor
  · rintro (hd | ⟨s,t,hst,ha,hk⟩)
    · have hdirect : (a,k)=oddRayDirect m :=
        (oddRayDirect_iff m a k).mpr hd
      refine ⟨0,?_⟩
      simpa only [oddRayIndexed,Fin.cases_zero] using hdirect.symm
    · have hs : s<m := by omega
      let i : Fin m := ⟨s,hs⟩
      have ht : t=m-s-1 := by omega
      refine ⟨Fin.succ i,?_⟩
      simp only [oddRayIndexed,Fin.cases_succ]
      change (FanArithmetic.p s (m-s-1),FanArithmetic.q s (m-s-1))=(a,k)
      rw [←ht,←ha,←hk]
  · rintro ⟨i,hi⟩
    cases i using Fin.cases with
    | zero =>
        left
        exact (oddRayDirect_iff m a k).mp
          (by simpa only [oddRayIndexed,Fin.cases_zero] using hi.symm)
    | succ i =>
        right
        have hs : i.val<m:=i.isLt
        let s:=i.val
        let t:=m-i.val-1
        have hst : m=s+t+1 := by dsimp [s,t];omega
        have heq : (FanArithmetic.p s t,FanArithmetic.q s t)=(a,k) := by
          simpa only [oddRayIndexed,Fin.cases_succ,FanArithmetic.source] using hi
        exact ⟨s,t,hst,(Prod.mk.inj heq).1.symm,(Prod.mk.inj heq).2.symm⟩

/-- Exact bijective finite enumeration of the full incoming fibre, hence
    precisely m+1 immediate predecessors, for every odd m. -/
theorem odd_ray_exact_incoming_count (m:Nat) (hm:m%2=1) :
    ∃ f : Fin (m+1) → Nat×Nat,
    Function.Injective f ∧
      ∀ a k, BB6.Agent46.secNext (a,k)=some (rayX m,rayY m) ↔
         ∃ i, f i=(a,k) := by
  exact ⟨oddRayIndexed m,oddRayIndexed_injective m,
    fun a k => oddRayIndexed_complete m a k hm⟩

#print axioms oddRayIndexed_injective
#print axioms odd_ray_exact_incoming_count
end BB6.Agent11Ray
