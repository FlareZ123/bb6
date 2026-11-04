import SecondRayEven0
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Ray
open BB6.Agent46

/-- The initial even parameter m=0 has exactly two possible source parents. -/
theorem zero_preimages_iff (a k:Nat) :
    secNext (a,k)=some (rayX 0,rayY 0) ↔
    (a,k)=(13,4) ∨ (a,k)=(1,7) := by
  have hd:rayD 0=16 := by decide
  have hx:rayX 0=5 := by decide
  have hy:rayY 0=10 := by decide
  rw [original_ray_parent_iff]
  rw [hd,hx,hy]
  constructor
  · rintro (hdir | he | hh)
    · left
      rcases hdir with ⟨ha,hk⟩
      apply Prod.ext <;> omega
    · right
      obtain ⟨ha,hk,n,hn,hcost⟩:=he
      have h2n:2^n=1 := by omega
      have hn0:n=0 := by
        cases n with
        | zero => rfl
        | succ n =>
            have hb:2≤2^(n+1) := by
              have hp:2^1≤2^(n+1) := Nat.pow_le_pow_right (by decide) (by omega)
              simpa using hp
            omega
      apply Prod.ext <;> omega
    · obtain ⟨ha,hregion,n,hn,hpow,hcost⟩:=hh
      have hn1:1≤n:=by omega
      have hp:4≤2^(n+1) := by
        have hl:2≤n+1:=by omega
        have hpowle:2^2≤2^(n+1) := Nat.pow_le_pow_right (by decide) hl
        simpa using hpowle
      have hmul:4*(a+3)≤2^(n+1)*(a+3) :=
        Nat.mul_le_mul_right (a+3) hp
      omega
  · rintro (hd | he)
    · left
      have ha:= (Prod.mk.inj hd).1
      have hk:= (Prod.mk.inj hd).2
      constructor <;> omega
    · right
      left
      have ha:= (Prod.mk.inj he).1
      have hk:= (Prod.mk.inj he).2
      refine ⟨ha,by omega,0,by decide,?_⟩
      omega

/-- Exactly two distinct inputs account for the complete m=0 fibre. -/
def zeroIndexed : Fin 2 → Nat×Nat :=
  Fin.cases (13,4) (fun _ => (1,7))

theorem zeroIndexed_injective : Function.Injective zeroIndexed := by
  intro i j h
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
          have hh : (13,4)=(1,7) := by
            simpa only [zeroIndexed,Fin.cases_zero,Fin.cases_succ] using h
          have hh1 := (Prod.mk.inj hh).1
          omega
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          have hh : (1,7)=(13,4) := by
            simpa only [zeroIndexed,Fin.cases_zero,Fin.cases_succ] using h
          have hh1 := (Prod.mk.inj hh).1
          omega
      | succ j =>
          exact congrArg Fin.succ (Subsingleton.elim i j)

theorem zero_exact_incoming_count :
    ∃ f : Fin 2 → Nat×Nat,
      Function.Injective f ∧
      ∀ a k, secNext (a,k)=some (rayX 0,rayY 0) ↔
        ∃ i:Fin 2, f i=(a,k) := by
  refine ⟨zeroIndexed,zeroIndexed_injective,?_⟩
  intro a k
  rw [zero_preimages_iff]
  constructor
  · rintro (hd | he)
    · exact ⟨0,by simpa only [zeroIndexed,Fin.cases_zero] using hd.symm⟩
    · exact ⟨Fin.succ 0,by simpa only [zeroIndexed,Fin.cases_succ] using he.symm⟩
  · rintro ⟨i,hi⟩
    cases i using Fin.cases with
    | zero =>
        left
        simpa only [zeroIndexed,Fin.cases_zero] using hi.symm
    | succ i =>
        right
        simpa only [zeroIndexed,Fin.cases_succ] using hi.symm

#print axioms zero_preimages_iff
#print axioms zero_exact_incoming_count
end BB6.Agent11Ray
