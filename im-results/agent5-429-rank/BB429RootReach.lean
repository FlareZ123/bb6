import BB429SourceBridge
import Lean.Elab.Tactic.Omega

namespace BB429RootReach
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA
open BB429SourceBridge

theorem sourceRun_add (i k : Nat) (s : HighLevelState) :
    sourceRun (i+k) s = (sourceRun i s).bind (sourceRun k) := by
  induction k with
  | zero => simp [sourceRun]
  | succ k ih =>
    rw [Nat.add_succ]
    simp only [sourceRun, ih]
    cases h : sourceRun i s with
    | none => simp [h]
    | some t => simp [h,sourceRun]

theorem source_orbit_reachable_even_seed (n a b : Nat)
    (h : sourceRun n (.J 0 0) = some (.J a b)) :
    ∃ i k u w, i+k=n ∧ sourceRun i (.J 0 0)= some (.J u w) ∧
      w%2=0 ∧ BB429Burst.firstRun k (u,w)= some (a,b) := by
  induction n generalizing a b with
  | zero =>
    simp only [sourceRun, Option.some.injEq, HighLevelState.J.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    exact ⟨0,0,0,0,rfl,rfl,rfl,rfl⟩
  | succ n ih =>
    change (sourceRun n (.J 0 0)).bind highLevelNext = some (.J a b) at h
    cases hp : sourceRun n (.J 0 0) with
    | none => simp [hp] at h
    | some p =>
      cases p with
      | J x y =>
        simp only [hp, Option.bind_some] at h
        by_cases hfirst : 2*x+3 ≤ y
        · have hs := source_first_step x y hfirst
          rw [hs] at h
          simp only [Option.some.injEq, HighLevelState.J.injEq] at h
          obtain ⟨rfl,rfl⟩ := h
          obtain ⟨i,k,u,w,his,hseed,hw,hprefix⟩ := ih x y hp
          refine ⟨i,k+1,u,w,by omega,hseed,hw,?_⟩
          change (BB429Burst.firstRun k (u,w)).bind BB429Burst.firstStep = _
          simp [hprefix,BB429Burst.firstStep,hfirst]
        · have heven : b%2=0 := exit_even x y a b (by omega) h
          have hr : sourceRun (n+1) (.J 0 0) = some (.J a b) := by
            change (sourceRun n (.J 0 0)).bind highLevelNext = _
            simpa only [hp, Option.bind_some] using h
          exact ⟨n+1,0,a,b,by omega,hr,heven,rfl⟩

def rootHalts : Prop :=
  ∃ n a b, sourceRun n (.J 0 0)= some (.J a b) ∧ highLevelNext (.J a b)= none

theorem root_halts_iff_sampled_exponential :
    rootHalts ↔
    ∃ i u w, sourceRun i (.J 0 0)= some (.J u w) ∧ w%2=0 ∧
      ∃ k, 2*u+w+3*k+13=4*((u+3)*2^k) := by
  constructor
  · rintro ⟨n,a,b,hr,hh⟩
    obtain ⟨i,k,u,w,his,hseed,hw,hprefix⟩ :=
      source_orbit_reachable_even_seed n a b hr
    have hgw := (source_none_iff a b).mp hh
    have he := (BB429Burst.gateway_iff_exponential u w k a b hprefix).mp hgw
    exact ⟨i,u,w,hseed,hw,⟨k,he⟩⟩
  · rintro ⟨i,u,w,hseed,hw,⟨k,he⟩⟩
    obtain ⟨j,a,b,hprefix,hh⟩ :=
      (source_burst_gateway_iff u w).mpr ⟨k,he⟩
    have hsr := firstRun_source u w j a b hprefix
    have ht : sourceRun (i+j) (.J 0 0)=some (.J a b) := by
      rw [sourceRun_add, hseed]
      exact hsr
    exact ⟨i+j,a,b,ht,hh⟩

#print axioms sourceRun_add
#print axioms source_orbit_reachable_even_seed
#print axioms root_halts_iff_sampled_exponential
end BB429RootReach
