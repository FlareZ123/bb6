import BusyBeaver.BB6.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA
import BB429Burst
import Lean.Elab.Tactic.Omega

namespace BB429SourceBridge
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Faithful source-level first-branch identity. -/
theorem source_first_step (u w : Nat) (h : 2*u+3 ≤ w) :
    highLevelNext (.J u w) = some (.J (2*u+3) (w-2*u-3)) := by
  simp only [highLevelNext]
  split
  · rfl
  · omega

/-- Native source-accelerator halting gateway, independent of model-copy definitions. -/
theorem source_none_iff (u w : Nat) :
    highLevelNext (.J u w) = none ↔ w+1=2*u := by
  constructor
  · intro h
    simp only [highLevelNext] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · split at h
              · cases h
              · split at h
                · cases h
                · cases h
            · split at h
              · omega
              · split at h
                · cases h
                · split at h
                  · split at h
                    · cases h
                    · cases h
                  · cases h
  · intro hl
    have hw : ¬(w ≥ 2*u+3) := by omega
    have hw2 : w ≠ 2*u+2 := by omega
    have hw1 : w ≠ 2*u+1 := by omega
    have hw0 : w ≠ 2*u := by omega
    have hp : w % 2 ≠ 0 := by omega
    have hd : u-w/2=1 := by omega
    simp only [highLevelNext]
    split
    · omega
    · simp [hw2, hw1, hw0, hp, hd]

/-- The source original accelerator's first-branch halting seeds are
    precisely the sparse exponential family. The first-run relation is the
    self-contained, source-matched first branch. -/
theorem source_burst_gateway_iff (u w : Nat) :
    (∃ n a b, BB429Burst.firstRun n (u,w) = some (a,b) ∧
      highLevelNext (.J a b) = none) ↔
    (∃ n, 2*u+w+3*n+13=4*((u+3)*2^n)) := by
  simpa only [source_none_iff] using (BB429Burst.burst_gateway_iff u w)

/-- Native source-level iterates, without suppressing any non-first branch. -/
def sourceRun (n : Nat) (s : HighLevelState) : Option HighLevelState :=
  match n with
  | 0 => some s
  | k+1 => (sourceRun k s).bind highLevelNext

/-- Every successful all-first-branch prefix is a genuine trajectory of
    the unmodified original source accelerator. -/
theorem firstRun_source (u w n a b : Nat)
    (h : BB429Burst.firstRun n (u,w) = some (a,b)) :
    sourceRun n (.J u w) = some (.J a b) := by
  induction n generalizing a b with
  | zero =>
    simp only [BB429Burst.firstRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    rfl
  | succ n ih =>
    simp only [BB429Burst.firstRun] at h
    cases hp : BB429Burst.firstRun n (u,w) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp, Option.bind_some] at h
      simp only [BB429Burst.firstStep] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        change (sourceRun n (.J u w)).bind highLevelNext = _
        rw [ih p.1 p.2 hp]
        simp only [Option.bind_some]
        exact source_first_step p.1 p.2 (by assumption)
      · simp at h

/-- Any exponential gate seed yields a genuine source-level accelerated
    halting witness, reached by a native finite iterate. -/
theorem gate_gives_source_halt (u w : Nat)
    (h : ∃ n, 2*u+w+3*n+13=4*((u+3)*2^n)) :
    ∃ n a b, sourceRun n (.J u w) = some (.J a b) ∧
      highLevelNext (.J a b) = none := by
  obtain ⟨n, a, b, hp, hg⟩ := (source_burst_gateway_iff u w).mpr h
  exact ⟨n, a, b, firstRun_source u w n a b hp, hg⟩


/-- Every non-first, nonhalting source branch returns an even second counter. -/
theorem exit_even (u w a b : Nat) (hexit : w < 2*u+3)
    (hn : highLevelNext (.J u w) = some (.J a b)) : b%2 = 0 := by
  simp only [highLevelNext] at hn
  split at hn
  · omega
  · split at hn
    · cases hn
      omega
    · split at hn
      · cases hn
        omega
      · split at hn
        · cases hn
          omega
        · split at hn
          · split at hn
            · cases hn
              omega
            · split at hn
              · cases hn
                omega
              · cases hn
                omega
          · split at hn
            · simp at hn
            · split at hn
              · cases hn
                omega
              · split at hn
                · split at hn
                  · cases hn
                    omega
                  · cases hn
                    omega
                · cases hn
                  omega

/-- Even second-counter burst seeds can only reach the gateway after odd many first steps. -/
theorem even_seed_odd_burst (u w n : Nat)
    (hw : w % 2 = 0)
    (he : 2*u+w+3*n+13 = 4*((u+3)*2^n)) : n % 2 = 1 := by
  omega

/-- Uniform mod-six value of any positive odd power of two. -/
theorem pow_two_odd_mod_six (k : Nat) : 2^(2*k+1) % 6 = 2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hpow : 2^(2*(k+1)+1) = 4 * 2^(2*k+1) := by
      calc
        2^(2*(k+1)+1) = 2^(2*k+1+2) := by congr 1 <;> omega
        _ = 2^(2*k+1) * 2^2 := Nat.pow_add _ _ _
        _ = 4 * 2^(2*k+1) := by omega
    rw [hpow]
    omega

/-- Every dangerous even burst seed belongs to residue 2 modulo 6. -/
theorem even_gateway_mod_six (u w n : Nat)
    (hw : w%2=0)
    (he : 2*u+w+3*n+13=4*((u+3)*2^n)) : w%6=2 := by
  have hn := even_seed_odd_burst u w n hw he
  obtain ⟨k,hk⟩ : ∃ k, n=2*k+1 := by
    exact ⟨n/2, by omega⟩
  subst n
  have hpow := pow_two_odd_mod_six k
  have hh : ((u+3)*2^(2*k+1))%6 = ((u+3)*2)%6 := by
    calc
      ((u+3)*2^(2*k+1))%6 = ((u+3)%6 * (2^(2*k+1)%6))%6 := Nat.mul_mod _ _ _
      _ = ((u+3)%6 * 2)%6 := by rw [hpow]
      _ = ((u+3)*2)%6 := by simp
  have hm : (4*((u+3)*2^(2*k+1)))%6 = (8*(u+3))%6 := by
    calc
      (4*((u+3)*2^(2*k+1)))%6 = (4%6 * (((u+3)*2^(2*k+1))%6))%6 := Nat.mul_mod _ _ _
      _ = (4%6 * (((u+3)*2)%6))%6 := by rw [hh]
      _ = (4*((u+3)*2))%6 := (Nat.mul_mod _ _ _).symm
      _ = (8*(u+3))%6 := by congr 1; omega
  have hemod := congrArg (fun t : Nat => t%6) he
  rw [hm] at hemod
  omega

/-- Native halting after a first-branch burst from an even seed forces
    the unique unshielded even residue modulo six. -/
theorem even_seed_source_gateway_mod_six (u w : Nat)
    (hw : w%2=0)
    (h : ∃ n a b, BB429Burst.firstRun n (u,w) = some (a,b) ∧
      highLevelNext (.J a b) = none) : w%6=2 := by
  obtain ⟨n,he⟩ := (source_burst_gateway_iff u w).mp h
  exact even_gateway_mod_six u w n hw he

#print axioms source_first_step
#print axioms source_none_iff
#print axioms source_burst_gateway_iff
#print axioms firstRun_source
#print axioms gate_gives_source_halt
#print axioms exit_even
#print axioms even_seed_odd_burst
#print axioms pow_two_odd_mod_six
#print axioms even_gateway_mod_six
#print axioms even_seed_source_gateway_mod_six

end BB429SourceBridge
